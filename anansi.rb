#! /usr/bin/ruby

require 'enumerator'
require 'set'
require 'stringio'
require 'tempfile'
require 'time'
require 'zlib'


#### Revision marker

VERSION = '0.8.1.20210711'


#### Resource extraction

## Resource extraction

# XXX: note that this would break if the last entry were an
# empty string, as each_slice(2) would then produce a
# single-entry list last, and to_h would barf upon seeing
# it.
RES = DATA.read.split(/^--8<--\s+([^\s].*?)\s*\n/)[1 .. -1].
    each_slice(2).to_h


#### Encoding validation

LATIN1_TEXT_CHARACTERS = [false] * 256
[0x20 .. 0x7E, 0xA0 .. 0xAC, 0xAE .. 0xFF,
    [0x0A, 0x0D]].each do |slab|
  slab.each do |c|
    LATIN1_TEXT_CHARACTERS[c] = true
  end
end

# Scans a string for a character that is not a Latin1
# printable or CR/LF/CRLF newline character, and returns its
# offset. If no such character was found, returns |nil|.
def find_latin1_error s
  (0 ... s.bytesize).each do |suboffset|
    c = s.getbyte suboffset
    return suboffset unless LATIN1_TEXT_CHARACTERS[c]
  end
  return nil
end


#### Splitting the input into lines

NST_HORIZONTAL = 0
NST_LF = 1
NST_CR = 2

def find_line_boundaries str
  state = NST_LF
  lines = []
  (0 ... str.bytesize).each do |i|
    b = str.getbyte i
    if state != NST_HORIZONTAL then
      lines.push i if state == NST_LF or (b != 0x0A)
    end
    state = case b
      when 0x0D then NST_CR
      when 0x0A then NST_LF
      else NST_HORIZONTAL
    end
  end
  lines.push str.bytesize
  return lines
end

def article_line_count
  return $article.line_boundaries.length - 1
end

def get_article_line i
  raise 'assertion failed' \
      unless i >= 0 and
          i + 1 < $article.line_boundaries.length
  start = $article.line_boundaries[i]
  stop = $article.line_boundaries[i + 1]
  return $article.content.byteslice start, stop - start
end

def each_article_line
  (0 ... article_line_count).each do |i|
    yield get_article_line i
  end
  return
end

def map_article_lines
  return (0 ... article_line_count).map do |i|
    yield get_article_line i
  end
end


#### Context-free vertical parser

## Appearance classification

def line_appearance l
  return (if reach(l) == 0 then :APP_EMPTY
      elsif could_be_adornment? l then :APP_ADORNMENT
      else
        case l.rstrip
          when /^\.\w+(\s|\z)/ then :APP_FIAT
          when /^-\s/ then :APP_UNINDENTED_BULLET
          when /^\s+-\s/ then :APP_INDENTED_BULLET
          when /^<[<].*>>\s*:\z/ then :APP_CAPER_SIGN
          when '::' then :APP_SPECIMEN_MARKER
          when /^\s/ then :APP_INDENTED
          else :APP_UNINDENTED
        end
      end)
end


## Adornment detection

ADORNMENT_CHARS = "*+-=^~"

def could_be_adornment? line
  e = reach line
  return false if e == 0
  return false unless ADORNMENT_CHARS.include? line[0]
  (1 ... e).each do |i|
    return false unless line[i] == line[0]
  end
  return true
end


## Line boundary detection

# For a non-empty line, returns the line's indentation --
# that is, the number of space characters in its beginning.
# For an empty line, including a line comprising a series of
# space characters, returns 0.
def indentation s
  (0 ... reach(s)).each do |i|
    return i if s[i] != ?\s
  end
  return 0
end

# We'll call 'reach' the length of a line with its
# trailing, but not leading, whitespace stripped. The term
# 'width' might be useful in the future, once we'll deal
# with Unicode and combining and double-width characters;
# we'll not use it yet in order to reduce such a future
# confusion.
def reach s, start = 0
  e = s.length
  e -= 1 if e > start and s[e - 1] == ?\r # skip the LF
  e -= 1 if e > start and s[e - 1] == ?\n # skip the CR
  while e > start and s[e - 1] == ?\s do # skip the spaces
    e -= 1
  end
  return e
end


#### Primary semantics scan

# The semantics scanning process assigns each line a
# semantic tag, considering its context. Note that some
# |:SEM_PACE| lines can be re-marked as |:SEM_SPECIMEN|
# later.

def assign_lines_prima_facie_semantics
  $article.semant = [nil] * article_line_count

  cur = Cursor.new
  # Search for the end of the header
  cur.go_to_line 0
  scan_and_mark_header cur
  $header_end = cur.line_index

  if cur.line_index > 0 and
      !cur.eof? and
      cur.current_line_appearance != :APP_EMPTY then
    cur.err "blank line missing after file header"
  end

  until cur.eof? do
    case cur.current_line_appearance
      when :APP_EMPTY then
        cur.mark_line_semantics :SEM_EMPTY
        cur.go_down
      when :APP_FIAT then
        cur.mark_line_semantics :SEM_FIAT
        cur.go_down
      when :APP_CAPER_SIGN then
        cur.mark_line_semantics :SEM_CAPER_SIGN
        cur.go_down
      when :APP_SPECIMEN_MARKER then
        cur.mark_line_semantics :SEM_SPECIMEN_MARKER
        cur.go_down
      when :APP_UNINDENTED_BULLET then
        scan_and_mark_bullet cur
      when :APP_INDENTED_BULLET then
        # This is a bit trickier, as both indented bullets
        # and indented code blocks are indented, and a
        # line that is indented and looks like it begins
        # with a bullet can start either. We'll consider
        # it a code block if:
        # - it's immediately preceded by a blank line, a
        #   caper sign, a specimen marker, top of the
        #   file, or top of the body; and
        # - scanning forward to a blank line or end of
        #   file, we will not encounter any unindented
        #   lines.
        # Otherwise, it must be an indented bullet.
        unless (cur.line_index == 0 or
                cur.line_index == $header_end or
                [:APP_EMPTY, :APP_CAPER_SIGN,
                        :APP_SPECIMEN_MARKER].include?(
                    cur.nearby_line_appearance(-1))) and
            scan_and_mark_pace_if_any cur then
          scan_and_mark_bullet cur
        end
      when :APP_INDENTED then
        unless scan_and_mark_pace_if_any cur then
          # Uh oh. The first line might have been
          # indented, but then, an unindented line must
          # have followed without an intervening blank
          # line. This can only be a paragraph!
          cur.err "paragraph inconsistently indented"
          scan_and_mark_paragraph_like cur
        end
      else
        if at_doubly_adorned_title? cur then
          cur.mark_line_semantics :SEM_TITLE_ADORNMENT
          cur.go_down
          cur.mark_line_semantics :SEM_ADORNED_TITLE
          cur.go_down
          cur.mark_line_semantics :SEM_TITLE_ADORNMENT
          cur.go_down
        elsif at_bottom_adorned_title? cur then
          cur.mark_line_semantics :SEM_ADORNED_TITLE
          cur.go_down
          cur.mark_line_semantics :SEM_TITLE_ADORNMENT
          cur.go_down
        else
          # Some other random unindented line.
          scan_and_mark_paragraph_like cur
        end
    end
  end
  return
end

# Leaves the traverser at the first line after the header.
def scan_and_mark_header cur
  cur.at_current_and_each_subsequent_line do
    case cur.current_line_appearance
      when :APP_UNINDENTED then
        break unless cur.current_line =~ /^\w+(?:-\w+)*:/
        cur.mark_line_semantics :SEM_METADATA
      when :APP_INDENTED, :APP_INDENTED_BULLET then
        break if cur.line_index == 0
        cur.mark_line_semantics :SEM_CONT
      else
        break
    end
  end
  return
end

def scan_and_mark_paragraph_like cur
  raise 'assertion failed' \
      if [:APP_EMPTY, :APP_BULLET, :APP_INDENTED_BULLET,
          :APP_FIAT].include? cur.current_line_appearance

  # Is this paragraph actually a title?
  if cur.current_line =~ /^\s*==+\s+[^\s]/ then
    cur.mark_line_semantics :SEM_HORIZONTAL_TITLE
  else
    cur.mark_line_semantics :SEM_PARAGRAPH
  end

  # Scan for the end of the paragraph
  loop do
    cur.go_down
    break if cur.eof? or
      [:APP_EMPTY, :APP_BULLET, :APP_INDENTED_BULLET,
          :APP_FIAT].include?(cur.current_line_appearance)
    cur.mark_line_semantics :SEM_CONT
  end

  return
end

def scan_and_mark_bullet cur
  raise 'assertion failed' \
      unless [:APP_INDENTED_BULLET, :APP_UNINDENTED_BULLET].
          include? cur.current_line_appearance

  cur.mark_line_semantics :SEM_BULLET
  base_indent = indentation cur.current_line

  loop do
    cur.go_down
    break if cur.eof? or
        indentation(cur.current_line) < base_indent or
        ![:APP_ADORNMENT, :APP_CAPER_SIGN,
            :APP_SPECIMEN_MARKER, :APP_INDENTED,
            :APP_UNINDENTED].include?(
                cur.current_line_appearance)
    cur.mark_line_semantics :SEM_CONT
  end

  return
end

# Checks if there's a pace starting at the current line in
# |cur|. (A series of indented lines may turn out to not
# form a pace if they are immediately, withut a separating
# blank line, followed by an unindented line.) If so, scans
# and marks the pace, and leaves |cur| pointing at the
# first line past it.  Otherwise, leaves |cur| pointing at
# the starting line.  Returns whether a pace was detected.
def scan_and_mark_pace_if_any cur
  raise 'assertion failed' \
          unless [:APP_INDENTED, :APP_INDENTED_BULLET].
      include? cur.current_line_appearance
  beginning = cur.line_index
  cur.go_down
  pace_end = nil
  loop do
    if (cur.eof? or
            cur.current_line_appearance == :APP_EMPTY) and
        [:APP_INDENTED, :APP_INDENTED_BULLET].include? cur.nearby_line_appearance(-1) then
      pace_end = cur.line_index
    end
    break if cur.eof? or
        ![:APP_INDENTED, :APP_INDENTED_BULLET, :APP_EMPTY].
            include? cur.current_line_appearance
    cur.go_down
  end
  if pace_end then
    cur.go_to_line beginning
    cur.mark_line_semantics :SEM_PACE
    loop do
      cur.go_down
      break if cur.line_index >= pace_end
      cur.mark_line_semantics :SEM_CONT
    end
    return true
  else
    cur.go_to_line beginning
    return false
  end
end

def at_doubly_adorned_title? cur
  return !cur.eof?(+2) &&
      cur.current_line_appearance == :APP_ADORNMENT &&
      reach(cur.current_line) >=
          reach(cur.nearby_line(+1)) &&
      at_bottom_adorned_title?(cur.nearby_line_cursor(+1))
end

def at_bottom_adorned_title? cur
  return !cur.eof?(+1) &&
      cur.current_line_appearance == :APP_UNINDENTED &&
      cur.nearby_line_appearance(+1) == :APP_ADORNMENT &&
      reach(cur.nearby_line(+1)) >=
          reach(cur.current_line) &&
      (cur.eof?(+2) or
          cur.nearby_line_appearance(+2) == :APP_EMPTY)
end


#### Outline scan

# The outline scan process analyses the different
# decorations and assigns a level to all titles, in
# the |$title_levels| global. It depends on the results from
# the primary semantics scn.

OUTLINE_DEPTH_LIMIT = 5

def perform_outline_scan
  adornment_levels = []

  $title_levels = {} # line-index => level

  cur = Cursor.new
  cur.at_each_line do
    adornment = parse_title_adornment cur
    if adornment then
      level = adornment_levels.index adornment
      if level then
        adornment_levels[level + 1 .. -1] = []
      else
        level = adornment_levels.length
        if level >= OUTLINE_DEPTH_LIMIT then
          cur.err "too deep for outline"
          # and convert the ostensible title into a
          # paragraph instead
          case cur.current_line_semantics
          when :SEM_ADORNED_TITLE
            if !cur.at_top? and
                cur.nearby_line_semantics(-1) ==
                    :SEM_TITLE_ADORNMENT then
              cur.mark_nearby_line_semantics -1,
                  :SEM_PARAGRAPH
              cur.mark_line_semantics :SEM_CONT
            else
              cur.mark_line_semantics :SEM_PARAGRAPH
            end
            cur.mark_nearby_line_semantics +1, :SEM_CONT
          when :SEM_HORIZONTAL_TITLE
            cur.mark_line_semantics :SEM_PARAGRAPH
          else
            raise 'assertion failed'
          end
          next
        end
        adornment_levels.push adornment
      end
      puts "#{(cur.line_index + 1).inspect}. level #{level.inspect}, #{adornment.inspect} #{get_article_line(cur.line_index).inspect}"
      $title_levels[cur.line_index] = level
    end
  end

  puts "DEBUG: $title_levels = #{$title_levels.inspect}"
  return
end

# Given cursor standing at a title line, extracts the shape
# of its adornment and returns it as a string. If the cursor
# is not standing at a title line, returns nil.
def parse_title_adornment cur
  case cur.current_line_semantics
    when :SEM_ADORNED_TITLE then
      if !cur.at_top? and
          cur.nearby_line_semantics(-1) ==
              :SEM_TITLE_ADORNMENT then
        top_adornment = cur.nearby_line(-1)[0]
      else
        top_adornment = ''
      end
      bottom_adornment = cur.nearby_line(+1)[0]
      adornment = [top_adornment, bottom_adornment] * '/'
      return adornment
    when :SEM_HORIZONTAL_TITLE then
      cur.current_line =~ /\A(==+)\s+/ or
          raise 'assertion failed'
      return $1
    else
      return nil
  end
end

#### Caper scan

# The caper scan collects the pace chains for each caper,
# the list of root capers and their declared root types,
# re-marks the |:SEM_PACE| blocks not in any caper as
# |:SEM_SPECIMEN|, and, building on |$title_levels|
# generated during the outline scan, handles implicit
# termination of caper signs when encountering a title level
# higher than where the caper sign originally appeared in.
def perform_caper_scan
  $capers = {} # name => [first-line-index-of-pace, ...]
  $caper_signs = {}
      # name => {type => [caper-sign-line-index, ...]}

  current_caper = nil
  current_caper_name = nil
  current_title_level = nil
  current_caper_title_level = nil

  cur = Cursor.new
  cur.at_each_line do
    case cur.current_line_semantics
    when :SEM_METADATA then
      cur.select_header_line_name
      ($capers[cur.region] ||= []).push cur.line_index
    when :SEM_CAPER_SIGN then
      root_type, current_caper_name =
          parse_caper_sign cur.current_line
      current_caper = $capers[current_caper_name] ||= []
      (($caper_signs[current_caper_name] ||= {})[
          root_type] ||= []).push cur.line_index
      current_caper_title_level = current_title_level
    when :SEM_SPECIMEN_MARKER then
      current_caper = nil
      current_caper_name = nil
      current_caper_title_level = nil
    when :SEM_PACE then
      if current_caper then
        current_caper.push cur.line_index
      else
        cur.mark_line_semantics :SEM_SPECIMEN
      end
    when :SEM_HORIZONTAL_TITLE, :SEM_ADORNED_TITLE then
      current_title_level = $title_levels[cur.line_index]
      raise 'assertion failed' unless current_title_level
      if current_caper and
          current_title_level < current_caper_title_level then
        current_caper = nil
        current_caper_title_level = nil
      end
    end
  end
  return
end

def debroket_caper_sign s
  s =~ /\A<[<]\s*(.*?)\s*>>\s*:\s*\r?\n?\z/ or
      raise 'assertion failed'
  return $1
end

def parse_caper_sign s
  caper_name = debroket_caper_sign s
  caper_name =~ /\A(?:(\.file|\.exec|\.task)\s+)?/
  root_type, caper_name = $1, $'
  return root_type, caper_name
end


#### Cursor

# A pointer to a line, and optionally, a position or a part
# of that line. Mutable; iterator functions can use the same
# Cursor instance to point sequentially at different things.
class Cursor
  attr_reader :line_index # 0-based, lines downwards
  attr_reader :offset # 0-based, across, optional
  attr_reader :end_offset # ditto

  def initialize line_index = nil,
      offset = nil, end_offset = nil
    raise 'assertion failed' \
        unless line_index.nil? or
            (0 .. article_line_count).include? line_index
    super()
    @line_index = line_index
    @offset = offset
    @end_offset = end_offset
    return
  end

  def dup
    return Cursor.new @line_index, @offset, @end_offset
  end

  def nearby_line_cursor delta
    return Cursor.new @line_index + delta
  end

  ## Vertical navigation

  def at_top?
    return @line_index > 0
  end

  def eof? delta = 0
    return @line_index + delta >= article_line_count
  end

  def go_to_line line_index
    raise 'assertion failed' \
        unless (0 .. article_line_count).include? line_index
    @line_index = line_index
    @offset = nil
    @end_offset = nil
    return
  end

  def go_down
    go_to_line @line_index + 1
    return
  end

  def at_each_line &thunk
    go_to_line 0
    at_current_and_each_subsequent_line &thunk
    return
  end

  def at_current_and_each_subsequent_line &thunk
    at_current_and_each_subsequent_line_until(
        article_line_count, &thunk)
    return
  end

  def at_current_and_each_subsequent_line_until j
    @offset = @end_offset = nil
    while @line_index < j do
      yield
      go_down
    end
    return
  end

  ## Horizontal navigation

  def go_right amount = 1
    go_to_offset @offset + amount
    return
  end

  def go_to_offset i
    raise 'assertion failed' \
        unless (0 .. current_line.length).include? i
    @offset = i
    if @end_offset and @end_offset < @offset then
      @end_offset = @offset
    end
    return
  end

  def move_end_left amount = 1
    new_end = @end_offset - amount
    raise 'assertion failed' \
        unless (0 .. current_line.length).include? new_end
    raise 'assertion failed' \
        unless @end_offset >= @offset
    @end_offset = new_end
    return
  end

  ## Selectors

  # Moves the offset of the current selection rightwards
  # until the first character of the selection is not a
  # space, a CR, or an LF character, or until the selection
  # will be empty.
  def lstrip_selection
    raise 'assertion failed' \
        if @offset.nil? or @end_offset.nil?
    raise 'assertion failed' \
        if @end_offset > current_line.length
    while @offset < @end_offset and
        " \r\n".include? current_line[@offset] do
      @offset += 1
    end
    return
  end

  def rstrip_selection
    raise 'assertion failed' \
        if @offset.nil? or @end_offset.nil?
    raise 'assertion failed' \
        if @end_offset > current_line.length
    while @end_offset > @offset and
        " \r\n".include? current_line[@end_offset - 1] do
      @end_offset -= 1
    end
    return
  end

  def select_line_stripped
    select_line_rstripped
    lstrip_selection
    return
  end

  def select_line_rstripped
    @offset = 0
    select_until_line_reach
    return
  end

  def select_until_line_reach
    raise 'assertion failed' \
        unless @offset
    @end_offset = reach current_line, @offset
    return
  end

  ## Retrieval

  def current_line
    return nearby_line(+0)
  end

  def nearby_line delta
    i = @line_index + delta
    raise 'assertion failed' \
        unless (0 ... article_line_count).include? i
    return get_article_line(i)
  end

  def current_char
    raise 'assertion failed' \
        unless @offset
    return current_line[@offset]
  end

  def region
    raise 'assertion failed' \
        unless @offset and @end_offset and \
            @end_offset >= @offset
    return current_line[@offset ... @end_offset]
  end

  def region_empty?
    raise 'assertion failed' \
        unless @offset and @end_offset and \
            @end_offset >= @offset
    return @end_offset == @offset
  end

  ## Referencing the location ...

  # ... for machine indexing
  def coord
    return [@line_index, @offset]
  end

  # ... for human perusal
  def loc
    result = $article.filename
    if @line_index then
      result += ":%i" % (@line_index + 1)
      if @offset then
        result += ".%i" % (@offset + 1)
        if @end_offset then
          # |@end_offset| is also tracked zero-based, but we
          # track it exclusively and report it inclusively,
          # so the +1-1 cancel out.
          result += "-%i" % @end_offset
        end
      end
    end
    return result
  end
end


#### Anansi-specific extensions to Cursor

class Cursor

  ## Annotation queries

  def current_line_appearance
    return $article.appear[@line_index]
  end

  def nearby_line_appearance delta
    i = @line_index + delta
    if (0 ... $article.appear.length).include? i then
      return $article.appear[i]
    else
      return nil
    end
  end

  def current_line_semantics
    return $article.semant[@line_index]
  end

  def nearby_line_semantics delta
    i = @line_index + delta
    if (0 ... $article.semant.length).include? i then
      return $article.semant[i]
    else
      return nil
    end
  end

  ## Annotation updates

  def mark_line_semantics tag
    mark_nearby_line_semantics 0, tag
  end

  def mark_nearby_line_semantics delta, tag
    i = @line_index + delta
    raise 'assertion failed' \
        unless (0 ... article_line_count).include? i
    $article.semant[i] = tag
    return
  end

  ## Syntax-related selectors

  def select_header_line_name include_colon: false
    raise 'assertion failed' \
        unless current_line_semantics == :SEM_METADATA
    @offset = 0
    colon = current_line.index ':'
    raise 'assertion failed' \
        unless colon
    @end_offset = include_colon ? colon + 1 : colon
    return
  end

  def select_header_line_body lstrip: true
    raise 'assertion failed' \
        unless [:SEM_METADATA, :SEM_CONT].\
            include? current_line_semantics
    select_line_rstripped
    if current_line_semantics == :SEM_METADATA then
      # Header line.  Let's skip over the field's name.
      colon = current_line.index ':'
      raise 'assertion failed' \
          unless colon
      @offset = colon + 1
    end
    lstrip_selection if lstrip
    return
  end

  ## Syntax-related traversal

  def at_each_block_line
    @offset = @end_offset = nil
    loop do
      yield
      go_down
      break if eof? or current_line_semantics != :SEM_CONT
    end
    return
  end

  def at_each_caper_pace caper_name
    $capers[caper_name]&.each do |i|
      go_to_line i
      yield
    end
    return
  end

  # From the current |@offset| onwards, stops at each code
  # line segment on this line, and yields whether it's a
  # transclusion reference or a literal segment.
  def at_each_code_line_segment_ahead
    raise 'assertion failed' \
        unless @offset
    while m = /<<.*?>>/.match(current_line, @offset) do
      if m.begin(0) == @offset then
        # We're standing at a reference. Yield it.
        @end_offset = m.end(0)
        yield true
      else
        # There's a reference somewhere ahead. Yield the
        # literal segment up to the reference.
        @end_offset = m.begin(0)
        yield false
      end
      @offset = @end_offset
    end
    # No more references.

    @end_offset = reach current_line
    yield false if @end_offset > @offset
    return
  end

  def at_each_transclusion caper_name
    at_each_caper_pace caper_name do
      at_each_block_line do
        go_to_offset 0
        at_each_code_line_segment_ahead do |refp|
          yield if refp
        end
      end
    end
    return
  end

  ## Error reporting

  def err msg
    $errors.flerr 'i', self, msg
    return
  end

  def perr msg
    $errors.flerr 'ip', self, msg
    return
  end

  def aerr msg
    $errors.flerr 'ia', self, msg
    return
  end
end


#### Dangling transclusion reference scan

def perform_dangling_transclusion_reference_scan
  cur = Cursor.new
  $caper_signs.each_key do |caper_name|
    cur.at_each_transclusion caper_name do
      referred_caper, sep = parse_ref cur.region
      # Note that header fields do not get
      # |$caper_signs| entries, only |$capers|
      # entries. Thus, we'll need to check both, as well as
      # overrides.

      unless $caper_signs[referred_caper] or
          $capers[referred_caper] or
          $cmdline[:overrides][referred_caper] then
        cur.err "<< %s >> is never defined" %
            referred_caper
        $transclusion_errors[cur.coord] = :undef
      end
    end
  end
  return
end


#### Transclusion reference scan

def perform_transclusion_reference_loop_scan
  Transclusion_Reference_Loop_Scanner.new.run
  return
end

class Transclusion_Reference_Loop_Scanner
  def run
    # We'll perform a depth-first scan through the reference
    # graph.

    @breadcrumbs = []

    # Collect capers to traverse
    @pending = Set.new $caper_signs.keys

    until @pending.empty? do
      current_caper = nil # for scoping
      @pending.each do |x|
        current_caper = x
        break
      end

      scan_caper current_caper
      raise 'assertion failed' \
          unless @breadcrumbs.empty?
    end
    return
  end

private

  def scan_caper caper_name
    # This is a recursive procedure, so we can't reuse a
    # Cursor inherited from an outer stack frame.
    cur = Cursor.new
    @breadcrumbs.push [caper_name, cur]
    loops_seen = false
    cur.at_each_transclusion caper_name do
      referred_caper, sep = parse_ref cur.region
      if $caper_signs[referred_caper] then
        ptr = @breadcrumbs.index{|frame|
            frame[0] == referred_caper}
        if not ptr.nil? then
          # We've found a transclusion loop.
          i = ptr
          while i < @breadcrumbs.length do
            referring_cursor = @breadcrumbs[i][1]
            coord = referring_cursor.coord
            unless $transclusion_errors[coord] then
              target = i + 1 < @breadcrumbs.length ? @breadcrumbs[i + 1][0] : referred_caper
              referring_cursor.err "<< %s >> -> << %s >>: transclusion loop" % [@breadcrumbs[i][0], target]
              $transclusion_errors[coord] = :loop
            end
            i += 1
          end
          loops_seen = true
        else
          scan_caper referred_caper
        end
      end
    end
    @breadcrumbs.pop
    # If this caper does not, even indirectly, transclude
    # any loops, it's a proper branch of the transclusion
    # tree, and does not need to be scanned again.
    @pending.delete caper_name unless loops_seen
    return
  end
end


#### Listing and pretty-printing facilities

APPEAR_ABBREV = {
  :APP_EMPTY => ' ',
  :APP_ADORNMENT => '~',
  :APP_FIAT => '#',
  :APP_UNINDENTED_BULLET => '-',
  :APP_INDENTED_BULLET => '+',
  :APP_CAPER_SIGN => '$',
  :APP_SPECIMEN_MARKER => ':',
  :APP_INDENTED => '/',
  :APP_UNINDENTED => "'",
}

SEMANT_ABBREV = {
  :SEM_EMPTY => ' ',
  :SEM_METADATA => 'm',
  :SEM_PARAGRAPH => 'p',
  :SEM_HORIZONTAL_TITLE => 'h',
  :SEM_CONT => '.',
  :SEM_CAPER_SIGN => 'c',
  :SEM_FIAT => 'f',
  :SEM_SPECIMEN_MARKER => 'x',
  :SEM_PACE => 'i', # i for indented
  :SEM_BULLET => 'b',
  :SEM_ADORNED_TITLE => 'a',
  :SEM_TITLE_ADORNMENT => 'z',
  :SEM_SPECIMEN => 's',
}

HL = {
  header_name: "\e[33;1m%s\e[0m",
  caper_sign: "\e[33;44;1m%s\e[0m",
  code: "\e[32m%s\e[0m",
  specimen_line: "\e[34;1m%s\e[0m",
  adornment: "\e[30;1m%s\e[0m",
  title: "\e[1m%s\e[0m",
  transclusion_wrapper: "\e[33;1m%s\e[0m",
  transclusion_core: "\e[32m%s\e[0m",
  invalid_transclusion_core: "\e[31m%s\e[0m",
  bullet: "\e[31;1m%s\e[0m",
  warning: "\e[31;1m%s\e[0m",
}

def prettify_line cur, block_type, is_last_line_of_block
  cur.select_line_rstripped
  l = cur.region
  line_type = cur.current_line_semantics
  if line_type == :SEM_METADATA then
    colon = l.index ?:
    raise 'assertion failed' \
        unless colon
    return HL[:header_name] % l[0 .. colon] +
        l[colon + 1 .. -1]
  elsif line_type == :SEM_CAPER_SIGN then
    return HL[:caper_sign] % l
  elsif line_type == :SEM_BULLET then
    return l.gsub(/\A(\s*)(-)(\s+.*)\z/){
      $1 + HL[:bullet] % $2 + $3}
  elsif line_type == :SEM_ADORNED_TITLE then
    return HL[:title] % l
  elsif line_type == :SEM_TITLE_ADORNMENT then
    return HL[:adornment] % l
  elsif block_type == :SEM_PACE then
    cl = ""
    cur.go_to_offset 0
    cur.at_each_code_line_segment_ahead do |refp|
      segment = cur.region
      unless refp then
        cl << HL[:code] % segment
      else
        valid = !$transclusion_errors[cur.coord]
        caper_name, sep, core_offset, core_end_offset =
            parse_ref segment
        cl <<
            HL[:transclusion_wrapper] %
                segment[0 ... core_offset] <<
            HL[valid ? :transclusion_core :
                    :invalid_transclusion_core] %
                segment[core_offset ... core_end_offset] <<
            HL[:transclusion_wrapper] %
                segment[core_end_offset .. -1]
      end
    end
    return cl
  elsif block_type == :SEM_SPECIMEN then
    return HL[:specimen_line] % l
  elsif block_type == :SEM_HORIZONTAL_TITLE then
    cl = ""
    if line_type == block_type then
      l =~ /\A(\s*)(==+)/
      cl << $1 << HL[:adornment] % $2
      l = $'
    end
    if is_last_line_of_block and
        l =~ /(\A|\s+)(==+)\z/ then
      cl << HL[:title] % $` << $1 << HL[:adornment] % $2
    else
      cl << HL[:title] % l
    end
    return cl
  else
    return l
  end
end

def list pretty, show_appearances, show_semantics
  $errors.each_main_error do |e|
    puts pretty ? HL[:warning] % e : e
  end
  lineno_template =
      '%%0%ii ' % article_line_count.to_s.length
  block_type = nil
  cur = Cursor.new
  bullet_tracker = Bullet_Nesting_Tracker.new
  bullet_tracker.start_handler = proc do
    puts '.bullet-list-start'
  end
  bullet_tracker.end_handler = proc do
    puts '.bullet-list-end'
  end
  cur.at_each_line do
    if cur.line_index == $header_end then
      puts '.header-end'
      list_header_overrides pretty
    end

    line_type = cur.current_line_semantics

    if line_type != :SEM_CONT then
      if line_type == :SEM_BULLET then
        cur.select_line_stripped
        bullet_tracker.track_bullet_list_nesting cur.offset
      else
        bullet_tracker.flush
      end
    end

    print lineno_template % (cur.line_index + 1)
    block_type = line_type \
        unless line_type == :SEM_CONT
    is_last_line_of_block = (cur.eof?(+1) or
        cur.nearby_line_semantics(+1) != :SEM_CONT)
    if show_appearances or show_semantics then
      if show_appearances then
        raise 'assertion failed' \
            unless APPEAR_ABBREV[cur.current_line_appearance]
        print APPEAR_ABBREV[cur.current_line_appearance]
      end
      if show_semantics then
        raise 'assertion failed' \
            unless SEMANT_ABBREV[line_type]
        print SEMANT_ABBREV[line_type]
      end
      print ' '
    end
    if pretty then
      puts prettify_line cur, block_type,
          is_last_line_of_block
    else
      cur.select_line_rstripped
      puts cur.region
    end
    $errors.each_line_error cur.line_index do |l|
      l = "! " + l
      puts pretty ? HL[:warning] % l : l
    end
  end
  bullet_tracker.flush
  return
end

def list_header_overrides pretty
  if $cmdline[:override_order] then
    $cmdline[:override_order].each do |name, data|
      if pretty then
        print '-: %s:' % name
      else
        print '-:' + HL[:header_name] % (name + ':')
      end
      print ' ' + data unless data.empty?
      puts
    end
  end
  return
end


#### Tangling

# Returns true upon successful tangling, and false in case
# any tangling loops or undefined capers were detected.
def tangle_caper name, sink, breadcrumbs, sep: nil
  success = true
  breadcrumbs.add name
  separate_paces = skip_once do
    sink.write sep if sep
    sink.newline; sink.newline
  end

  override = $cmdline[:overrides][name]
  override&.each do |entry|
    separate_paces.call
    sink.write entry
  end

  cur = Cursor.new
  cur.at_each_caper_pace name do
    separate_paces.call
    separate_lines = skip_once{sink.newline}

    case cur.current_line_semantics
    when :SEM_METADATA then
      unless override then
        cur.at_each_block_line do
          separate_lines.call
          cur.select_header_line_body
          sink.write cur.region
        end
      end
    when :SEM_PACE then
      at_each_pace_line cur do
        separate_lines.call
        cur.at_each_code_line_segment_ahead do |refp|
          unless refp then
            sink.write cur.region
          else
            caper_name, sep = parse_ref cur.region
            if $transclusion_errors[cur.coord] == :undef then
              marker_loc = sink.write_placeholder cur.region
              cur.perr "%s: marked dangling reference" %
                      marker_loc
              success = false
            elsif breadcrumbs.include? caper_name then
              cur.err "broke transclusion loop << %s >> -> << %s >>" %
                      [name, caper_name]
              marker_loc = sink.write_placeholder cur.region
              cur.perr "%s: marked transclusion loop break" %
                      marker_loc
              success = false
            else
              # A proper transclusion.
              sink.hold_indent do
                success &&= tangle_caper caper_name,
                    sink, breadcrumbs, sep: sep
              end
            end
          end
        end
      end
    else
      raise 'assertion failed'
    end
  end
  breadcrumbs.delete name
  return success
end

def at_each_pace_line cur, &thunk
  raise 'assertion failed' \
      unless cur.current_line_semantics == :SEM_PACE \
          or cur.current_line_semantics == :SEM_SPECIMEN
  indent = cur.pace_indent
  cur.at_each_block_line do
    if cur.current_line_appearance != :APP_EMPTY then
      cur.go_to_offset indent
    else
      cur.go_to_offset 0
    end
    yield
  end
  return
end

def parse_ref ref
  if ref =~ /\A<<\s*
      (.*?)
      (?:\s+\.sep\(([^()]+)\))?
      \s*>>\z/ix then
    caper_name, sep, name_begin, name_end =
        $1, $2, $~.begin(1), $~.end(1)
  else
    raise 'assertion failed'
  end
  return caper_name, sep, name_begin, name_end
end

class Cursor
  # Determines the indentation of the pace whose first line
  # is currently focused. Does not change the focus.
  def pace_indent
    return dup._pace_indent
  end

  # Scans through the current pace's lines and determines
  # the indentation. Leaves focus at the pace's last line.
  # Meant to be only called from |pace_indent|.
  def _pace_indent
    so_far = nil
    at_each_block_line do
      next if current_line_appearance == :APP_EMPTY
      candidate = indentation current_line
      if so_far.nil? or candidate < so_far then
        so_far = candidate
      end
    end
    return so_far
  end
end

def skip_once &thunk
  firstp = true
  return proc do
    if firstp then
      firstp = false
    else
      yield
    end
  end
end


## Root handling

# Returns whether the tangling was successful.
def tangle_file name
  success = nil # for scoping
  open name, 'w' do |port|
    sink = Sink.new port, name
    success = tangle_caper name, sink, Set.new
    sink.implicit_newline
    make_executable port \
        if $caper_signs[name].include? '.exec'
  end
  return success
end

def make_executable file
  unless Gem.win_platform? then
    mode = file.stat.mode & 0o7777
    mode |= ((mode & 0o444) >> 2) & ~File.umask
    file.chmod mode
  end
  return
end

# Returns whether all the tangling was successful.
def tangle_default_files
  success = true
  have_any_files = false
  $caper_signs.each_pair do |name, types|
    # FIXME-5: once we have support for optionality, exclusion
    # of tasks here should be done by marking them as
    # optional during the caper scan
    if (types.include?('.file') or
            types.include?('.exec')) and
        not types.include?('.task') then
      have_any_files = true
      success &&= tangle_file name
    end
  end
  # FIXME-6: once we have optional files, differentiate
  # between this and "all files are optional"

  # Note that this is not /exactly/ an error condition: if
  # we have no files and tangle nothing, we'll have
  # succeeded. It's more of a case of /Error! No error!/
  xerr "%s: no files in this web" % $article.filename \
      unless have_any_files
  return success
end

# Returns whether all the tangling was successful.
def tangle_requested_files names
  success = true
  names.each do |name|
    types = $caper_signs[name]
    if !types.nil? and
        (types.include?('.file') or
            types.include?('.exec')) then
      success &&= tangle_file name
    else
      xerr "%s: no such file" % name
      success = false
    end
  end
  return success
end

def list_roots
  $caper_signs.each_pair do |name, types|
    type_tag = %w{.task .exec .file}.
        find{|t| types.include?  t}
    puts type_tag + ' ' + name \
        if type_tag
  end
  return
end


## The tangling sink interface

class Sink
  attr_accessor :file
  attr_accessor :filename # used only for error messages
  attr_accessor :eol_hook

  # Note that |nil| can be supplied as the file in case a
  # dry run is needed.
  def initialize file, filename, newline: "\n"
    super()
    @file = file; @filename = filename; @newline = newline
    @x = 0; @indent = [0]
    @lineno = 1
    @eol_hook = nil
    return
  end

  # Writes the given (assumed purely horizontal, i. e., not
  # containing any linebreaks) string into the target file
  # and updates |@x| accordingly. If this is the first
  # explicit thing on the current line, also writes out the
  # current indentation.
  def write s
    unless s.empty? then
      if @x == 0 then
        @file&.write " " * @indent[-1]
        @x = @indent[-1]
      end
      @file&.write s
      @x += s.length
    end
    return
  end

  # Calls |write| with the given string, but returns a
  # formatted range suitable for indicating the locus of the
  # written string in an (error) message.
  def write_placeholder s
    x_before = @x == 0 ? @indent[-1] : @x
    write s
    return "%s:%i.%i-%i" % [@filename, @lineno,
        x_before + 1, @x]
  end

  # Writes out a linebreak. If |@eol_hook| is set, calls it
  # first. Updates |@x| accordingly.
  def newline
    @eol_hook&.call
    @file&.write @newline
    @x = 0
    @lineno += 1
    return
  end

  # Calls |linebreak| if we're not at the beginning of a
  # line. Useful for treating linebreaks as terminators,
  # like the Unix convention goes, rather than as
  # separators.
  def implicit_newline
    newline if @x != 0
    return
  end

  # Temporarily -- for the duration of executing the
  # supplied block -- maintains the current horizontal
  # position as the indentation margin.
  def hold_indent &block
    @indent.push @x != 0 ? @x : @indent[-1]
    begin
      yield
    ensure
      @indent.pop
    end
  end
end


#### Task execution

# Returns whether the task was executed successfully.
def execute_task task
  unless $caper_signs[task] then
    xerr "#{task}: no such task"
    return false
  end
  unless $caper_signs[task].include? '.task' then
    xerr "#{task}: not a task"
    return false
  end

  sandbox = Dir.mktmpdir
  begin
    puts "DEBUG: created sandbox directory #{sandbox.inspect}"
    file = Tempfile.new task, sandbox
    puts "DEBUG: file.path = #{file.path.inspect}"
    quasifile = StringIO.new
    sink = Sink.new quasifile, task
    first_line = nil # for scoping
    sink.eol_hook = proc do
      first_line = quasifile.string
      sink.file = file
      file.write first_line
      sink.eol_hook = nil
    end
    tangling_success = tangle_caper task, sink, Set.new
    success &&= tangling_success
    sink.implicit_newline
    file.flush
    unless tangling_success then
      # FIXME-8: once we'll have recipes, this might in some
      # contexts need to be a listable error instead
      xerr "#{task}: won't execute a task tangled " + \
          "with placeholders"
      return false
    end
    make_executable file
    if first_line =~ /\A#!/ then
      argv = $'.split
    else
      argv = [ENV['SHELL'] || '/bin/sh']
    end
    argv.push file.path
    return execute_and_check argv, chdir: sandbox,
        taskname: task
  ensure
    unless clean_up_sandbox_dir sandbox then
      xerr "#{sandbox}: sandbox clean-up failed"
      return false
    end
  end
end

def clean_up_sandbox_dir d
  successful = true
  Dir.entries(d).each do |e|
    next if %w{. ..}.include? e
    qe = File.join d, e
    if File.directory? qe then
      successful &= clean_up_sandbox_dir qe
    else
      begin
        File.unlink qe
      rescue SystemCallError => err
        xerr "#{qe}: unlink: #{err.class.new.to_s}"
        successful = false
      end
    end
  end
  begin
    Dir.rmdir d
  rescue SystemCallError => err
    xerr "#{d}: rmdir: #{err.class.new.to_s}"
    successful = false
  end
  return successful
end

# |taskname| is used only for error reporting. If not given,
# defaults to |argv[0]|.
def execute_and_check argv, chdir: nil, taskname: nil
  # FIXME-9: once we have recipes, the errors generated by
  # this function will need, in some contexts, to be
  # listable errors instead
  $stderr.puts "DEBUG: argv = #{argv.inspect}"
  kwargs = {}
  kwargs[:chdir] = chdir unless chdir.nil?
  unless Gem.win_platform? then
    kwargs[:in] = '/dev/null'
  else
    # Yes, this works on Windows.
    kwargs[:in] = 'nul:'
  end
  taskname = argv[0] if taskname.nil?

  # Temporarily disable SIGINT; if one were to arise while
  # we're running an external process, we'll want the child
  # process to handle it, and in the parent process, just
  # wait until it's done
  previous_sigint_behaviour = Signal.trap 'INT', 'IGNORE'
  pid = spawn(*argv, **kwargs)
  _, ps = Process.wait2 pid
  Signal.trap 'INT', previous_sigint_behaviour

  if ps.exited? then
    if ps.exitstatus == 0 then
      return true
    else
      xerr "%s: exited with %i" %
          [taskname, ps.exitstatus]
      return false
    end
  elsif ps.signaled? then
    msg = "died of SIG%s" % Signal.signame(ps.termsig)
    msg << " and dumped core" if ps.coredump?
    xerr "%s: %s" % [taskname, msg]
    return false
  else
    # The only remaining alternative result from |waitpid|
    # is that we stopped the child via ptrace, and we did
    # not.
    raise 'assertion failed'
  end
end


#### Weaving

def collect_header_values
  header_values = {}
  current_header = nil
  cur = Cursor.new
  cur.go_to_line 0
  while !cur.eof? and \
      cur.current_line_semantics == :SEM_METADATA do
    cur.select_header_line_name
    name = cur.region
    current_header = header_values[name] ||= ""

    at_each_header_field_line cur do
      current_header << " " \
          unless current_header.empty?
      current_header << cur.region
    end
  end
  puts "DEBUG: header_values = #{header_values.inspect}"
  return header_values
end

# Given a cursor at a |:SEM_METADATA| line, yields with each
# of this header field's content line, except the first one
# if it's empty, selected. Returns leaving the cursor at the
# line immediately past the end of this header field's line.
def at_each_header_field_line cur
  raise 'assertion failed' \
      unless cur.current_line_semantics == :SEM_METADATA
  loop do
    cur.select_header_line_body
    yield unless cur.region_empty?
    cur.go_down
    break if cur.eof? or \
        cur.current_line_semantics != :SEM_CONT
  end
  return
end

AUTOMATIC_METADATA = {
  'Paper-size' => 'a5',
  'Title' => 'Untitled',
  'Author' => 'A Humble Author',
  'Date' => 'Undated',
  'Pace-colour' => '#008000',
  'Specimen-colour' => '#000080',
}

def get_macro_candidate_from_override name
  # Overrides are single-line, but a single value can be
  # overridden multiple times. For weaving macro
  # processing purposes, we'll join these together with
  # a single space.
  return $cmdline[:overrides][name]&.join ' '
end

def prepare_macros
  macros = {}

  header_values = collect_header_values

  header_fetcher = proc do |name|
    header_values[name] \
        if header_values[name]
  end

  # Some macros are copied over from the article's header
  # (or its overrides.)

  universal_acceptor = proc{|v| v}

  paper_size_acceptor = proc do |v|
    v = v.downcase
    v if %w{a4 a5}.include? v
  end

  [
    ['Title', :plain, universal_acceptor],
    ['Author', :plain, universal_acceptor],
    ['Company', :plain, universal_acceptor],
    ['Date', :plain, universal_acceptor],
    ['Paper-size', :paper_size, paper_size_acceptor],
  ].each do |key, type, acceptor|
    value = nil
    value_source = nil
    falling_back = false
    candidate = get_macro_candidate_from_override key
    if candidate then
      candidate = acceptor.call candidate
      if candidate then
        # acceptable
        value = candidate
        value_source = :override
      else
        xerr "invalid override for %s" % key
        falling_back = true
      end
    end

    candidate = header_fetcher.call key
    if candidate then
      candidate = acceptor.call candidate
      if candidate then
        # acceptable
        if value.nil? then
          value = candidate
          value_source = :header
        end
      else
        if value.nil? then
          # FIXME: this should point to the header field
          xerr "invalid header value for %s" % key
          falling_back = true
        else
          # FIXME: this should point to the header field
          xerr "warning: invalid header value for overridden %s"
        end
      end
    end

    if value.nil? then
      value = AUTOMATIC_METADATA[key]
      value_source = :default
    end

    if falling_back then
      case value_source
      when :header then
        xerr "falling back to the header value for %s" % key
      when :default then
        xerr "falling back to the default value for %s" % key
      end
    end

    macros[key] = value
  end
  
  AUTOMATIC_METADATA.each_pair do |k, v|
    macros[k] ||= v
  end

  macros['anansi-version'] = VERSION

  macros['infilename'] =
      escape_ascii_nonprintables $cmdline[:infilename]

  macros['mtime'] = $article.mtime.iso8601
  macros['crc32'] = '%08x' % $article.crc32

  %w{Pace-colour Specimen-colour}.each do |name|
    rgb = nil
    if header_values[name] then
      rgb = parse_rgb header_values[name]
      if rgb.nil? then
        xerr "unknown value for %s, reverting to %s" %
            [name, AUTOMATIC_METADATA[name]]
      end
    end
    rgb ||= parse_rgb AUTOMATIC_METADATA[name]
    macros[name] = '#%02x%02x%02x' % rgb
    macros[name + '.tex'] = fractional_rgb rgb
  end

  pp macros # DEBUG

  return macros
end

def prepare_tex_weaving_macros
  macros = prepare_macros

  macros['main_font_family'] = 'ibm-plex-serif'
  macros['mono_font_family'] = 'ibm-plex-mono'

  case macros['Paper-size']
  when 'a5' then
    macros['geometry'] = 'margin=7.5mm,tmargin=12mm'
  when 'a4' then
    macros['geometry'] = 'margin=20mm'
  else
    raise 'assertion failed'
  end

  macros['specify-main-font'] =
      specify_font('main', macros['main_font_family'])
  macros['specify-mono-font'] =
      specify_font('mono', macros['mono_font_family'])

  # Some macros need to be escaped before use.

  # For now, we'll encode author, company, and date in hard
  # mode in order to properly deal with the interference
  # between English spacing and initials (as well as
  # German-style ordinal-indicating periods). (FIXME-16:
  # eventually, the |.~| mark-up construct should take care
  # of these things.)
  [
    ['Title', true],
    ['Author', false],
    ['Company', false],
    ['Date', false],
  ].each do |name, soft|
    if macros.include? name then
      macros[name + '.tex'] = texescape macros[name],
              soft: soft \
          if macros[name]
    end
  end

  # We'll only define |error-summary| if there are errors.
  # This way, |ifdef| can check error presence in a sensible
  # way.
  macros['error-summary'] = method :weave_error_summary \
      if $errors.have_main_errors?
  macros['narrative'] = method :weave_tex_narrative

  return macros
end

def escape_ascii_nonprintables s
  result = ""
  s.each_byte do |ch|
    case ch
    when 0x5C then
      result << "\\\\"
    when 0x20 .. 0x7F then
      result << ch.chr
    else
      result << "\\x%02X" % ch
    end
  end
  return result
end

def parse_rgb s
  if s =~ /\A#([\dabcdef]{3}){1,2}\z/i then
    if s.length == 4 then
      red, green, blue = s[1 ..  -1].
          scan(/./).map(&:hex).map{|i| i * 0x11}
    elsif s.length == 7 then
      red, green, blue = s[1 ..  -1].
          scan(/../).map(&:hex)
    else
      raise 'assertion failed'
    end
    return [red, green, blue]
  else
    # unparseable
    return nil
  end
end

def fractional_rgb rgb
  return rgb.map{|c| '%.3f' % (c * 1.0 / 0xFF)} * ', '
end

def weave_tex
  open $weave_output_root + '.tex', 'w' do |f|
    apply_template RES['tex-template'],
        prepare_tex_weaving_macros, f
  end
  return
end

def weave_html
  macros = prepare_macros
  # FIXME: escape infilename in HTML way, and remember to
  # take care of double dashes
  open $weave_output_root + '.html', 'w' do |f|
    apply_template RES['html-template'], macros, f,
        colons: true
  end
  return
end

def texescape_region cur, f, soft: false
  f.write texescape(cur.region, soft: soft)
  return
end

def weave_error_summary f
  if $errors.have_main_errors? then
    $errors.each_main_error do |e|
      f.puts
      f.puts texescape(e, soft: true)
    end
  end
  return
end

TEX_NARRATIVE_HANDLERS = {}

TEX_NARRATIVE_HANDLERS[[:SEM_PARAGRAPH, :line]] = proc do
  @cur.select_line_stripped
  texescape_region @cur, @port, soft: true
  @port.puts
end
TEX_NARRATIVE_HANDLERS[[:SEM_PARAGRAPH, :end]] = proc do
  @port.puts '\par'
end
TEX_NARRATIVE_HANDLERS[[:SEM_CAPER_SIGN, :line]] = proc do
  # FIXME-17: there should be method that selects the
  # debroketed part of the caper sign line
  @port.puts '\capersign{%s}' %
      texescape(debroket_caper_sign(@cur.current_line))
end
TEX_NARRATIVE_HANDLERS[[:SEM_FIAT, :line]] = proc do
  @cur.select_line_stripped
  @port.write '\fiat{'
  texescape_region @cur, @port
  @port.puts '}'
end
TEX_NARRATIVE_HANDLERS[[:SEM_METADATA, :line]] = proc do
  @port.write '\leftline{\ttfamily'
  if @cur.current_line_semantics == :SEM_METADATA then
    # The first line of this header field. Print the
    # field's name in boldface.
    @port.write '\textbf{'
    @cur.select_header_line_name include_colon: true
    texescape_region @cur, @port
    @port.write '}'
  else
    # Separate the |\ttfamily| from the upcoming
    # TeXencoded data, which may start with a letter.
    # Note that TeX ignores this whitespace, other
    # than for tokenisation.
    @port.write ' ' # just for TeX token separation
  end
  @cur.select_header_line_body lstrip: false
  texescape_region @cur, @port
  @port.write '}'
  @port.puts
end

TEX_NARRATIVE_HANDLERS[[:SEM_EMPTY, :line]] =
    TEX_NARRATIVE_HANDLERS[[:SEM_SPECIMEN_MARKER, :line]] =
    TEX_NARRATIVE_HANDLERS[[:SEM_TITLE_ADORNMENT, :line]] =
    proc do
  # just skip
end

TEX_NARRATIVE_HANDLERS[[:SEM_BULLET, :start]] = proc do
  @port.write '\item '
end

TEX_NARRATIVE_HANDLERS[:bullet_list_start] = proc do
  @port.puts '\begin{itemize}'
end

TEX_NARRATIVE_HANDLERS[:bullet_list_end] = proc do
  @port.puts '\end{itemize}'
end

TEX_NARRATIVE_HANDLERS[[:SEM_BULLET, :line]] = proc do
  @cur.select_line_stripped
  if @cur.current_line_semantics == :SEM_BULLET then
    # remove the leading dash
    raise 'assertion failed' \
        unless @cur.current_char == ?-
    @cur.go_right
    @cur.lstrip_selection
  end
  texescape_region @cur, @port, soft: true
  @port.puts
end

TEX_NARRATIVE_HANDLERS[[:SEM_PACE, :start]] = proc do
  @code_indent = @cur.pace_indent
  @port.puts '\begin{pace}'
end

TEX_NARRATIVE_HANDLERS[[:SEM_PACE, :line]] = proc do
  @cur.go_to_offset [@code_indent,
      @cur.current_line.length].min
  @cur.select_until_line_reach
  unless @cur.region_empty? then
    @cur.at_each_code_line_segment_ahead do |refp|
      unless refp then
        @port.write texescape(@cur.region)
      else
        valid = !$transclusion_errors[@cur.coord]
        subcur = @cur.dup
        subcur.go_right 2
        subcur.move_end_left 2
        subcur.lstrip_selection
        subcur.rstrip_selection
        @port.write(valid ? '\transclude' :
            '\badtransclude')
        @port.write '{'
        @port.write texescape(subcur.region)
        @port.write '}'
      end
    end
    @port.puts
  else
    @port.puts '\medskip'
  end
end

TEX_NARRATIVE_HANDLERS[[:SEM_PACE, :end]] = proc do
  @port.puts '\end{pace}'
end

TEX_NARRATIVE_HANDLERS[[:SEM_SPECIMEN, :start]] = proc do
  @code_indent = @cur.pace_indent
  @port.puts '\begin{specimen}'
end

TEX_NARRATIVE_HANDLERS[[:SEM_SPECIMEN, :line]] = proc do
  @cur.go_to_offset [@code_indent,
      @cur.current_line.length].min
  @cur.select_until_line_reach
  l = @cur.region
  unless l.empty? then
    @port.write texescape(l)
    @port.puts
  else
    @port.puts '\medskip'
  end
end

TEX_NARRATIVE_HANDLERS[[:SEM_SPECIMEN, :end]] = proc do
  @port.puts '\end{specimen}'
end

TEX_NARRATIVE_HANDLERS[[:SEM_ADORNED_TITLE, :line]] = proc do
  level = $title_levels[@cur.line_index]
  title_macro = LATEX_TITLE_LEVELS[level]
  raise 'assertion failed' \
      unless title_macro
  @cur.select_line_rstripped
  @port.write '\%s{' % title_macro
  texescape_region @cur, @port, soft: true
  @port.puts '}'
  @cur.go_down
end

TEX_NARRATIVE_HANDLERS[[:SEM_HORIZONTAL_TITLE, :start]] = proc do
  level = $title_levels[@cur.line_index]
  title_macro = LATEX_TITLE_LEVELS[level]
  raise 'assertion failed' \
      unless title_macro
  @port.print '\%s{' % title_macro
  @separate_lines = skip_once{@port.puts}
end

TEX_NARRATIVE_HANDLERS[[:SEM_HORIZONTAL_TITLE, :line]] = proc do
  @separate_lines.call
  @cur.select_line_rstripped
  if @cur.current_line_semantics == :SEM_HORIZONTAL_TITLE then
    # remove the leading boundary series of equal signs
    while !@cur.region_empty? and @cur.current_char == ?= do
      @cur.go_right
    end
    @cur.lstrip_selection
  end
  texescape_region @cur, @port, soft: true
end

TEX_NARRATIVE_HANDLERS[[:SEM_HORIZONTAL_TITLE, :end]] = proc do
  @port.puts '}'
end

class Bullet_Nesting_Tracker
  attr_accessor :start_handler
  attr_accessor :end_handler

  def initialize
    super()
    # When unwinding the bullet stack, we'll be referring to
    # the _second_ last entry. In order to avoid having to
    # check the element count for the 'Is the stack empty?'
    # condition, we'll use two sentinel values.
    @bullet_stack = [-2, -1]
    @start_handler = nil
    @end_handler = nil
    return
  end

  def track_bullet_list_nesting new_offset
    if new_offset > @bullet_stack.last then
      # A new bullet nesting level.
      @start_handler&.call
      @bullet_stack.push new_offset
    else
      # Note that when the stack contains no nested bullets,
      # @bullet_stack[-2] will still be negative because we
      # have two sentinel values, and thus lower than any
      # valid |new_offset|.
      while new_offset < @bullet_stack[-2] do
        @bullet_stack.pop
        @end_handler&.call
      end
      raise 'assertion failed' \
        unless new_offset <= @bullet_stack[-1]
      @bullet_stack[-1] = new_offset \
          if new_offset >= 0
    end
    return
  end

  def flush
    track_bullet_list_nesting -2
    return
  end
end

class Narrative_Weaving_Context
  attr_reader :bullet_tracker

  def initialize cur, port
    super()
    @cur = cur
    @port = port
    return
  end

  def handle event
    handler = TEX_NARRATIVE_HANDLERS[event]
    instance_eval &handler \
        if handler
    return
  end
end

def weave_tex_narrative f
  cur = Cursor.new
  cur.go_to_line 0
  ctx = Narrative_Weaving_Context.new cur, f
  bullet_tracker = Bullet_Nesting_Tracker.new
  bullet_tracker.start_handler = proc do
    ctx.handle :bullet_list_start
  end
  bullet_tracker.end_handler = proc do
    ctx.handle :bullet_list_end
  end
  block_type = nil
  until cur.eof? do
    line_type = cur.current_line_semantics
    if line_type != :SEM_CONT then
      ctx.handle [block_type, :end] \
          if block_type

      if line_type == :SEM_BULLET then
        @cur.select_line_stripped
        bullet_tracker.track_bullet_list_nesting @cur.offset
      else
        bullet_tracker.flush
      end

      ctx.handle [line_type, :start]
    else
      line_type = block_type
    end
    ctx.handle [line_type, :line]
    block_type = line_type
    cur.go_down
  end
  ctx.handle [block_type, :end] \
      if block_type
  bullet_tracker.flush
  return
end

def specify_font slot, family_name
  family = FONT_FAMILIES[family_name]
  result = "\\set%sfont[\n" % slot
  family.each_pair do |key, name|
    next if key == 'Vanilla'
    result << "  %sFont={%s},\n" % [key, name]
  end
  raise "font family without Vanilla: #{family.inspect}" \
      unless family.has_key? 'Vanilla'
  result << "]{%s}" % family['Vanilla']
  # mind the lack of newline at the end
  return result
end

FONT_FAMILIES = {
  'iosevka-aile' => {
    'Vanilla' => 'iosevka-aile-regular.ttf',
    'Bold' => 'iosevka-aile-bold.ttf',
    'Italic' => 'iosevka-aile-italic.ttf',
    'BoldItalic' => 'iosevka-aile-bolditalic.ttf',
    'Slanted' => 'iosevka-aile-oblique.ttf',
    'BoldSlanted' => 'iosevka-aile-boldoblique.ttf',
  },

  'iosevka-aile-light' => {
    'Vanilla' => 'iosevka-aile-light.ttf',
    'Bold' => 'iosevka-aile-semibold.ttf',
    'Italic' => 'iosevka-aile-lightitalic.ttf',
    'BoldItalic' => 'iosevka-aile-semibolditalic.ttf',
    'Slanted' => 'iosevka-aile-lightoblique.ttf',
    'BoldSlanted' => 'iosevka-aile-semiboldoblique.ttf',
  },

  'iosevka-fixed-extended' => {
    'Vanilla' => 'iosevka-fixed-extended.ttf',
    'Bold' => 'iosevka-fixed-extendedbold.ttf',
    'Italic' => 'iosevka-fixed-extendeditalic.ttf',
    'BoldItalic' => 'iosevka-fixed-extendedbolditalic.ttf',
    'Slanted' => 'iosevka-fixed-extendedoblique.ttf',
    'BoldSlanted' => 'iosevka-fixed-extendedboldoblique.ttf',
  },

  'ibm-plex-sans' => {
    'Vanilla' => 'IBMPlexSans-Text.otf',
    'Bold' => 'IBMPlexSans-Bold.otf',
    'Italic' => 'IBMPlexSans-TextItalic.otf',
    'BoldItalic' => 'IBMPlexSans-BoldItalic.otf',
    'Slanted' => 'IBMPlexSans-TextItalic.otf',
    'BoldSlanted' => 'IBMPlexSans-BoldItalic.otf',
  },

  'ibm-plex-serif' => {
    'Vanilla' => 'IBMPlexSerif-Regular.otf',
    'Bold' => 'IBMPlexSerif-Bold.otf',
    'Italic' => 'IBMPlexSerif-Italic.otf',
    'BoldItalic' => 'IBMPlexSerif-BoldItalic.otf',
    'Slanted' => 'IBMPlexSerif-TextItalic.otf',
    'BoldSlanted' => 'IBMPlexSerif-BoldItalic.otf',
  },

  'ibm-plex-serif-text' => {
    'Vanilla' => 'IBMPlexSerif-Text.otf',
    'Bold' => 'IBMPlexSerif-Bold.otf',
    'Italic' => 'IBMPlexSerif-TextItalic.otf',
    'BoldItalic' => 'IBMPlexSerif-BoldItalic.otf',
    'Slanted' => 'IBMPlexSerif-TextItalic.otf',
    'BoldSlanted' => 'IBMPlexSerif-BoldItalic.otf',
  },

  'ibm-plex-mono' => {
    'Vanilla' => 'IBMPlexMono-Regular.otf',
    'Bold' => 'IBMPlexMono-Bold.otf',
    'Italic' => 'IBMPlexMono-TextItalic.otf',
    'BoldItalic' => 'IBMPlexMono-BoldItalic.otf',
    'Slanted' => 'IBMPlexMono-TextItalic.otf',
    'BoldSlanted' => 'IBMPlexMono-BoldItalic.otf',
  },
}

def texescape s, soft: false
  return s.gsub(/[ "\#$%&'<>\\^_{|}~-]/) do
    case $&
    when ' ' then soft ? ' ' : '~'
    when "'" then '\textquotesingle{}'
    when '"' then '\textquotedbl{}'
    when '"', '\\', '^', '~' then '\\char%i{}' % $&.ord
    when '|' then '\\char%i{}' % 0x007C
    when '-', '<', '>', "'" then "{#$&}"
    when '_' then '\\_'
    else
      '\\' + $&
    end
  end
end

LATEX_TITLE_LEVELS = %w{chapter section subsection
    subsubsection paragraph}


#### Template engine for weaving

def apply_template template, defs, f, colons: false
  ifdef_pass_level = 0
  ifdef_fail_level = 0

  re = !colons ? /<([^<>]*)>/ : /<:([^<:>]*):>/
  template.split(re, -1).
      each_with_index do |s, i|
    if i.even?
      f.write s if ifdef_fail_level == 0
    else
      case s
      when /\Aifdef\s+/ then
        if ifdef_fail_level == 0 and
            defs.include?($') then
          ifdef_pass_level += 1
        else
          ifdef_fail_level += 1
        end
      when 'endif' then
        if ifdef_fail_level != 0 then
          ifdef_fail_level -= 1
        elsif ifdef_pass_level != 0 then
          ifdef_pass_level -= 1
        else
          raise 'assertion failed: misplaced <endif>'
        end
      else
        if ifdef_fail_level == 0 then
          raise 'assertion failed: <%s> not defined' % s \
              unless defs.include? s
          definition = defs[s]
          if definition.respond_to? :call then
            definition.call f
          else
            f.write definition
          end
        end
      end
    end
  end
  if ifdef_pass_level != 0 or ifdef_fail_level != 0 then
    raise 'assertion failed: missing <endif>'
  end
  return
end


#### Command line interface

## Complaint interface

# The external errors are those having to do with the
# infrastructure or the specific request from the command
# line: no such file, trying to tangle an untangleable, etc.
# They are printed strictly to stderr, and not collected to
# be included in listings. Most, but not all, are fatal.
def xerr msg
  $stderr.puts "an: #{msg}"
  return
end

# The localised errors, or line errors, or listing errors,
# are issues with specific parts of the input article(s).
# They are only printed in the listing.
# FIXME-21: they should also be printed in the woven output.

class Error_Manager
  def initialize
    super()
    @main = []
    @by_line_index = {}
    return
  end

  # Currently defined flags are:
  # - 'a' for Annotation,
  # - 'i' for Inline, and
  # - 'p' for Prefix included.
  def flerr flags, cur = nil, msg
    raise 'assertion failed' \
        unless flags =~ /\A[tip]+\z/
    if cur then
      raise 'assertion failed' \
          unless cur.is_a? Cursor
      msg = "%s: %s" % [cur.loc, msg] \
          unless flags.include? 'p'
    else
      # No cursor given, so 'p' does not make sense.
      raise 'assertion failed' \
          if flags.include? 'p'
    end
    unless flags.include? 'a' then
      unless $cmdline[:generate_listing] then
        xerr msg
      end
      @main.push msg
    end
    if flags.include? 'i' then
      raise 'assertion failed' \
          unless cur and cur.line_index
      (@by_line_index[cur.line_index] ||= []).push msg
    end
    return
  end

  def have_main_errors?
    return !@main.empty?
  end

  def each_main_error &thunk
    @main.each &thunk
    return
  end

  def each_line_error line_index, &thunk
    @by_line_index[line_index]&.each &thunk
    return
  end
end

$errors = Error_Manager.new

## Command line metadata

require 'getoptlong'

# A user-friendlier wrapper around |GetoptLong|.
class Command_Line_Interface
  def initialize &zone
    super()
    @declarations = []
    @handlers = {}
    instance_eval &zone if zone
    return
  end

  def option cname, *other_names, &handler
    case handler.arity
    when 0 then
      gol_type = GetoptLong::NO_ARGUMENT
    when 1 then
      gol_type = GetoptLong::REQUIRED_ARGUMENT
    else
      raise 'assertion failed'
    end
    @declarations.push [cname, *other_names, gol_type]
    @handlers[cname] = handler
    return
  end

  def flag cname, *other_names, attr: nil, value: true
    attr ||= cname.gsub(/^-+/, '').gsub('-', '_').to_sym
    option cname, *other_names do
      $cmdline[attr] = value
    end
    return
  end

  def parse!
    begin
      GetoptLong.new(
        *@declarations,
      ).each do |opt, arg|
        @handlers[opt].call arg
      end
    rescue GetoptLong::InvalidOption,
        GetoptLong::MissingArgument
      # the error has already been reported by |GetoptLong#each|
    end
    return
  end
end

$cli = Command_Line_Interface.new do
  flag '--show-appearances', '-A'
  flag '--show-semantics', '-S'
  flag '--statistics', '-s'
  flag '--list-roots', '-l'
  flag '--tangle', '-t'
  flag '--pretty-print', '-P'

  option '--execute', '-e' do |arg|
    ($cmdline[:execute] ||= []).push arg
  end

  flag '--weave', '-w'
  flag '--weave-html', '-W'
  flag '--tex'
  flag '--no-tex', '-T', attr: :tex, value: false

  option '--set', '-:' do |arg|
    i = find_latin1_error arg
    if i then
      xerr "--set: invalid Latin-1 <%02X>" %
          arg.getbyte(i)
      exit 1
    end
    # If we were to support multi-line header overrides,
    # we'd have to make a bunch of tricky decisions about
    # handling them with no obvious answers, and with
    # minimal benefits. Better to not support them at all,
    # until and unless a strong use case were to show up.
    i = arg.index(?\x0A) || arg.index(?\x0D)
    if i then
      xerr "--set: newline in header override" %
          arg.getbyte(i)
      exit 1
    end
    # The same restrictions apply to |--set| as to file
    # header names.
    unless arg =~ /^(\w+(?:-\w+)*):\s*/ then
      xerr "--set: invalid field name"
      exit 1
    end
    name, data = $1, $'.strip

    ($cmdline[:override_order] ||= []).push [name, data]
    ($cmdline[:overrides][name] ||= []).push data

    # FIXME-22: use these for control value overriding in
    # weaving
    # FIXME-23: use these in tangling
    # FIXME-24: mark these overrides in the weaved output
  end
end


## Command line parser

$cmdline = {tex: true, overrides: {}}

$cli.parse!

$cmdline[:generate_listing] =
    $cmdline[:show_appearances] ||
    $cmdline[:show_semantics] ||
    $cmdline[:pretty_print]


if ARGV.length < 1 then
  xerr "input file not given"
  exit 1
end

if $cmdline[:tangle] then
  $cmdline[:files_to_tangle] = ARGV[1 .. -1] \
    if ARGV.length > 1
else
  if ARGV.length > 1 then
    xerr "too many arguments"
    exit 1
  end
end

if ARGV[0] != '-' then
  # We'll have a real file in $cmdline[:infilename].
  $cmdline[:infilename] = ARGV[0]
  $cmdline[:infile] = nil
  $cmdline[:article_filename] = ARGV[0]
  $weave_output_root = File.basename($cmdline[:infilename]).
      sub(/\.an\z/i, '')
else
  # We'll put |$stdin| into $cmdline[:infile], and a
  # placeholder in $cmd[:infilename] and
  # $cmdline[:article_filename].
  $stdin.binmode
  $cmdline[:infile] = $stdin
  $cmdline[:infilename] = '(stdin)'
  $cmdline[:article_filename] = '(stdin)'
  $weave_output_root = 'untitled'
end


#### Main

Article = Struct.new :filename, :content, :line_boundaries,
    :mtime, :crc32, :appear, :semant

$article = Article.new
$article.filename = $cmdline[:article_filename]

if $cmdline[:infile] then
  $article.content = $cmdline[:infile].read
  $article.mtime = $cmdline[:infile].stat.mtime
else
  File.open $cmdline[:infilename], 'rb' do |f|
    $article.content = f.read
    $article.mtime = f.stat.mtime
  end
end

$article.crc32 = Zlib.crc32 $article.content
$article.line_boundaries =
    find_line_boundaries $article.content

# Check that the input is a proper Latin-1 text file
offset = 0
each_article_line do |l|
  suboffset = find_latin1_error l
  if suboffset then
    xerr "%s:@0x%x: invalid Latin-1 <%02X>" % [
        $article.filename, offset + suboffset,
        l.getbyte(suboffset)]
    exit 1
  end
  offset += l.bytesize
end

$article.appear = map_article_lines do |l|
  line_appearance l
end

assign_lines_prima_facie_semantics
perform_outline_scan
perform_caper_scan

$transclusion_errors = {}
perform_dangling_transclusion_reference_scan
perform_transclusion_reference_loop_scan

puts "DEBUG: $capers = #{$capers.inspect}"

def check_root_status_consistency
  cur = Cursor.new
  $caper_signs.each_pair do |name, types|
    if types.length > 1 then
      $errors.flerr '', "<< %s >> has ambiguous root status" %
          [$article.filename, name]
      $caper_signs[name].each_pair do |root_type, line_indices|
        line_indices.each do |i|
          cur.go_to_line i
          # To the operator, we'll report a single list of
          # all the conflicting root declarations.
          $errors.flerr '', cur,
              "<< %s >> declared as %s here" % [name,
                  root_type || 'non-root']
          # Inline, next to each definition, we'll report
          # the other root types used, but not their
          # locations.
          $caper_signs[name].each_key do |other_root_type|
            next if other_root_type == root_type
            cur.aerr "<< %s >> is declared as %s elsewhere" %
                [name, other_root_type || 'non-root']
          end
        end
      end
    end
  end
  return
end

check_root_status_consistency

if $cmdline[:list_roots] then
  list_roots
end

success = true

if $cmdline[:tangle] then
  if $cmdline[:files_to_tangle].nil? then
    success &&= tangle_default_files
  else
    success &&= tangle_requested_files $cmdline[:files_to_tangle]
  end
end

if $cmdline[:execute] then
  $cmdline[:execute].each do |task|
    success &&= execute_task task
  end
end

if $cmdline[:generate_listing] then
  list $cmdline[:pretty_print], $cmdline[:show_appearances],
      $cmdline[:show_semantics]
end

if $cmdline[:weave] then
  weave_tex
  if $cmdline[:tex] then
    argv = 'xelatex', $weave_output_root + '.tex'
    pdf_filename = $weave_output_root + '.pdf'
    puts "DEBUG: argv = #{argv.inspect}"
    3.times do
      unless execute_and_check argv then
        # FIXME-26: complain at the proper level here, too
        success = false
        break
      end
      unless File.exists? pdf_filename then
        xerr 'xelatex failed to generate %s' % pdf_filename
        success = false
      end
    end
  end
end

if $cmdline[:weave_html] then
  weave_html
end

if $cmdline[:statistics] then
  puts "%i line(s)" % article_line_count
  puts "%i caper(s)" % $capers.length
end

exit success ? 0 : 1

__END__
--8<-- tex-template
% Generated by Anansi/<anansi-version> from <infilename>
% (crc32: <crc32>, mtime: <mtime>).
% You might not want to edit this file by hand.

\documentclass[<Paper-size>paper,11pt,twoside,article]%
    {memoir}
\usepackage{fontspec}
\usepackage{xcolor}
\usepackage{imakeidx}
<specify-main-font>
<specify-mono-font>
\definecolor{pace}{rgb}{<Pace-colour.tex>}
\definecolor{specimen}{rgb}{<Specimen-colour.tex>}
\definecolor{badtransclude}{rgb}{0.8, 0, 0}
\usepackage[<geometry>]{geometry}
\usepackage{fancyhdr}

\parindent=25pt

\def\codeblocksetup{%
  \obeylines%
  \parindent=0pt%
  \ttfamily%
  \setbox0=\hbox{~~}%
  \leftskip=\wd0%
}


\newenvironment{pace}
  {\codeblocksetup\color{pace}}
  {}

\newenvironment{specimen}
  {\codeblocksetup\color{specimen}}
  {}

% let's stick to ascii, okay riley?
%\def\broketed#1{\char10216~#1~\char10217}
%        % U+27E8 #1 U+27E9

\def\broketed#1{\textless~#1~\textgreater}

\def\capersign#1{\leftline{\texttt{\broketed{#1}:}}}

\def\transclude#1{\textit{\broketed{#1}}}
\def\badtransclude#1{\textcolor{badtransclude}{%
    \transclude{#1}}}

\def\fiat#1{\leftline{\textbf{\texttt{#1}}}}

\newenvironment{werr}
  {\bgroup %
    \obeylines%
    \advance\leftskip by 20pt %
    \parindent=-20pt %
    \noindent %
  }{\egroup}

\pagestyle{fancy}
\fancyhf{}
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0.4pt}
\fancyfoot[LE,RO]{\textsl{\thepage}}
\headsep=2pt
\footskip=20pt
\raggedbottom

\title{<Title.tex>}
\author{<Author.tex><ifdef Company.tex> \\
  <Company.tex><endif>}
\date{<Date.tex>}

\begin{document}

\maketitle

% FIXME-27: shouldn't header fields go here, at least if
% we're tangling just one file?

\begin{KeepFromToc}
<ifdef error-summary>
\section*{Error summary}

\begin{werr}
<error-summary>
\end{werr}

<endif>
\tableofcontents
\end{KeepFromToc}

\cleardoublepage

<narrative>
\end{document}
--8<-- html-template
<!doctype html>
<html>
  <!-- Generated by Anansi/<:anansi-version:> from
       <:infilename:> -->
<head>
<title></title>
</head>
<body>
<article>
<h1></h1>
</article>
</body>
</html>
