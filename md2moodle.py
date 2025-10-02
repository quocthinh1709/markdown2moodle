# Markdown to Moodle XML 
#
# This script parses a markdown file (containing quizes) and outputs Moodle's XML Quiz format.
#
# The specification of Moodle XML format: https://docs.moodle.org/38/en/Moodle_XML_format
#
# Please see README.md for markdown format details and script usage.
#
# Credits to https://github.com/goFrendiAsgard/markdown-to-moodle-xml.git for the original code.
# This is a significant evolution of his code, but maintains the basic ideas.
#
# ---
#
# This script contains all classes and functions used to implement a finite state machine (FSM)
# used to parse a markdown file. This enables a more robust approach to the parsing mechanism,
# together with localized error detection in the parsed file.
#
# The currently implemented FSM is illustrated in 'markdown2moodle.png' and can be further
# extended to include other states.
#
# ---
#
# This script is organized into the following sections:
#
# Section 0 - Global constants
# Section 1 - REGEX patterns, helpers and transformations over text 
# Section 2 - Quiz class, helper functions and constants
# Section 3 - FSM implementation
# Section 4 - FSM Markdown Parser
# Section 5 - Main 

import os
import sys
import re
import hashlib
import random
import json
import base64
from markdown import markdown
import webbrowser

import tkinter as tk
from tkinter import ttk
import tkinter.filedialog
import pathlib

# To prettify xml
import xml.dom.minidom


if sys.version_info[0] == 3:
    from urllib.request import urlopen
else:
    from urllib import urlopen


checkbox_table_border_state = True
checkbox_suffer_state = True
answer_numbering_value = 'none'
error_message = None

######################################################################
# Section 0 - Global constants
######################################################################

CONFIG = {
    # Produce debugging information while parsing
    'debug' : False,

    # Place table borders through css style?
    'table_border' : False,
    
    # quiz answer numbering | allowed values: 'none', 'abc', 'ABCD' or '123'
    'answer_numbering' : 'none', 
    # quiz shuffle answers | 1 -> true ; 0 -> false
    'shuffle_answers' : '1',

    # in single answer questions, the penalty to apply to a wrong answer in % [0,1]
    'single_answer_penalty_weight' : 0, #e.g., 0.25 = 25% 

    # pygments code snapshot generator
    'pygments.font_size' : 16,
    'pygments.line_numbers' : False,

    # pygments code snapshot | additional dump to disk of generated images
    'pygments.dump_image' : False,
    'pygments.dump_image_id' : 1, #e,g, 1.png and incremented for each image

}

######################################################################
# Section 1 - REGEX patterns, helpers and transformations over text 
######################################################################

##
# REGEX PATTERNS

NEW_LINE = '\n'
HEADER_PATTERN = re.compile(r'^\s*# (.*)$')
QUESTION_PATTERN = re.compile(r'^(\s*)\*(\s)(.*)$')
CORRECT_ANSWER_PATTERN = re.compile(r'^(\s*)-(\s)!(.*)$')
WRONG_ANSWER_PATTERN = re.compile(r'^(\s*)-(\s)(.*)$')
SWITCH_PRE_TAG_PATTERN = re.compile(r'^```.*$')
EMPTY_LINE_PATTERN = re.compile(r'^\s*$')
IMAGE_PATTERN = re.compile(r'!\[.*\]\((.+)\)')
MULTI_LINE_CODE_PATTERN = re.compile(r'```(.*)\n([\s\S]+?)```', re.MULTILINE)
SINGLE_LINE_CODE_PATTERN = re.compile(r'`([^`]+)`')
# question mark in the regex implies that it is not greedy
# If you have ... $...$ ... $...$..., with the question mark, both parts will be replaced, giving ... REPL ... REPL   ...
# Without question mark, you have one replacement from the first to the last $.
SINGLE_DOLLAR_LATEX_PATTERN = re.compile(r'\$(.+?)\$')
# re.DOTALL implies that meta character . also corresponds to \n
# Hence, between $$ and $$, there may have several lines
# question mark in the regex implies that it is not greedy
# If you have ... $$...$$ ... $$...$$..., with the question mark, both parts will be replaced, giving ... REPL ... REPL   ...
# Without question mark, you have one replacement from the first to the last $$.
DOUBLE_DOLLAR_LATEX_PATTERN = re.compile(r'\$\$(.+?)\$\$', re.DOTALL)
BLOCKCODE_PATTERN = re.compile(r'^(\s*)```(.*)$')

TABLE_PATTERN = re.compile(r'\[\[\[(.*)\n([\s\S]+?)\]\]\]', re.MULTILINE )



LIGHT_BG = "#ECF0F3"
BUTTON_BG = "#3688D0"
TEXT_FG = "#2272B7"
icon_path = f"D:\VSCode\Text2QTI\QTIIcon.ico"

def main():
    
    file_name = ''
    global checkbox_table_border_state
    global checkbox_suffer_state

    window = tk.Tk()
    window.configure(bg=LIGHT_BG)
    window.title('Convert Markdown to Moodle XML')
    #window.geometry("800x600")
    window.minsize(width=800, height=600)
    window.maxsize(width=800, height=600)
    window.iconbitmap(icon_path)
    # Bring window to front and put in focus
    window.iconify()
    #window.update()
    window.deiconify()

    # Window grid setup
    current_row = 0
    column_count = 4


    header_label = tk.Label(
        window,
        #text='Convert Markdown to Moodle XML',
        text='Chuyển đổi định dạng Markdown sang Moodle XML',
        font=(None, 20),
        fg = TEXT_FG,
        bg = LIGHT_BG,
        highlightthickness=0
    )
    header_label.grid(
        row=current_row, column=0, columnspan=column_count, padx=(30, 30), pady=(30, 10),
        sticky='nsew',
    )
    current_row += 1
    header_link_label = tk.Label(
        window,
        text='Github',
        font=(None, 10), fg='blue', cursor='hand2',
        bg= LIGHT_BG,
        highlightthickness=0
    )
    header_link_label.bind('<Button-1>', lambda x: webbrowser.open_new('https://github.com/brunomnsilva/markdown2moodle'))
    header_link_label.grid(
        row=current_row, column=0, columnspan=column_count, padx=(30, 30),
        sticky='nsew',
    )
    current_row += 1
    last_dir = None
    def browse_files():
        nonlocal file_name
        nonlocal last_dir
        if last_dir is None:
            initialdir = pathlib.Path('~').expanduser()
        else:
            initialdir = last_dir
        file_name = tkinter.filedialog.askopenfilename(
            initialdir=initialdir,
            title='Select a quiz file',
            filetypes=[('Quiz files', '*.md;*.txt')],
        )
        if file_name:
            if last_dir is None:
                last_dir = pathlib.Path(file_name).parent
            file_browser_button.config(text=f'"{os.path.basename(file_name)}"', fg='white')
        else:
            file_browser_button.config(text=f'<none selected>', fg='red')

    file_browser_button = tk.Button(
        window,
        text='Chọn file (md/txt)',
        fg='white',
        bg = BUTTON_BG,
        font=(None, 14),
        width=50,
        command=browse_files,
    )
    file_browser_button.grid(
        row=current_row, column=0, columnspan= 4, padx=(50, 50), pady=(10, 20),
        sticky='nsew',
    )

    current_row += 1
    config_frame = tk.Frame(
        window,
        width=100, height=50,
        borderwidth=0, relief='sunken', bg='white',
    )
    config_frame.grid(
        row=current_row, column=0, columnspan=column_count, padx=(50, 50), pady=(10, 10),
        sticky='nsew',
    )

    # Tạo một biến để lưu trạng thái của ô kiểm
    checkbox_suffer_state = tk.BooleanVar()
    
    checkbox_suffer_state.set(True)  # Đặt giá trị mặc định của ô kiểm là True (được chọn)

    # Tạo ô kiểm
    checkbox_suffer = tk.Checkbutton(config_frame, text="Đảo thứ tự đáp án", 
                              variable=checkbox_suffer_state,
                              bg = 'white',
                              fg = TEXT_FG) 
    #checkbox.pack(pady=10)
    checkbox_suffer.grid(
        row=0, column = 0, padx=(30, 30),
        sticky='nsew',
    )

    checkbox_table_border_state = tk.BooleanVar()
    
    checkbox_table_border_state.set(True)  # Đặt giá trị mặc định của ô kiểm là True (được chọn)

    # Tạo ô kiểm
    checkbox_table_border = tk.Checkbutton(config_frame, text="Định dạng viền cho bảng", 
                              variable=checkbox_table_border_state,
                              bg = 'white',
                              anchor='w',
                              fg = TEXT_FG) 
    #checkbox.pack(pady=10)
    checkbox_table_border.grid(
        row=0, column = 1, padx=(30, 30),
        sticky='nsew',
    )
    list_type_label = tk.Label(
        config_frame,
        text=f'Kiểu đánh đáp án',
        fg = TEXT_FG,
        bg = 'white',
        highlightthickness=0
    )
    list_type_label.grid(
        row=1, column=0, padx=(30, 30), pady=(5, 5),
        sticky='nsew',
    )

    # Tạo một danh sách các lựa chọn cho combobox
    options = ['abc', 'ABCD', '123', 'none']
    # Tạo combobox
    combo_box = ttk.Combobox(config_frame, values=options)
    combo_box.grid(
        row=1, column = 1, padx=(35, 30), pady=(5, 5),
        sticky='nsew',
    )
    combo_box.configure(foreground=TEXT_FG) 
    #combo_box.pack(pady=10)

    # Đặt giá trị mặc định cho combobox
    combo_box.set(options[3])

    # Hàm được gọi khi người dùng thay đổi giá trị của combobox
    def on_combobox_change(event):
        global answer_numbering_value
        answer_numbering_value = combo_box.get()
        #print("Đã chọn:", answer_numbering_value)

    combo_box.bind("<<ComboboxSelected>>", on_combobox_change)

    current_row += 1
    def run():
        global CONFIG
        suffer_char = '1'
        if(checkbox_suffer_state):
            suffer_char = '1'
        else:
            suffer_char = '0'
        CONFIG = {
        # Produce debugging information while parsing
        'debug' : False,

        # Place table borders through css style?
        'table_border' : checkbox_table_border_state,
        
        # quiz answer numbering | allowed values: 'none', 'abc', 'ABCD' or '123'
        'answer_numbering' : answer_numbering_value, 
        # quiz shuffle answers | 1 -> true ; 0 -> false
        'shuffle_answers' : suffer_char,

        # in single answer questions, the penalty to apply to a wrong answer in % [0,1]
        'single_answer_penalty_weight' : 0, #e.g., 0.25 = 25% 

        # pygments code snapshot generator
        'pygments.font_size' : 16,
        'pygments.line_numbers' : False,

        # pygments code snapshot | additional dump to disk of generated images
        'pygments.dump_image' : False,
        'pygments.dump_image_id' : 1, #e,g, 1.png and incremented for each image
        }




        run_message_text.delete(1.0, tk.END)
        run_message_text['fg'] = 'gray'
        run_message_text.insert(tk.INSERT, 'Starting...')
        run_message_text.update()

        global error_message #= None

        if not file_name:
            error_message = 'Must select a quiz file'
            run_message_text.delete(1.0, tk.END)
            run_message_text.insert(tk.INSERT, error_message)
            run_message_text['fg'] = 'red'
            return

        file_path = pathlib.Path(file_name)
        try:
            with open(file_path, "r", encoding="utf-8-sig") as file:
                text = file.read()
            #print(text)
        except FileNotFoundError:
            #error_message = f'File "{file_path}" does not exist.'
            error_message = f'File "{file_path}" không tồn tại.'
        except PermissionError as e:
            #error_message = f'File "{file_path}" cannot be read due to permission error. Technical details:\n\n{e}'
            error_message = f'File "{file_path}" không đọc được do không có quyền. Chi tiết:\n\n{e}'
        except UnicodeDecodeError as e:
            #error_message = f'File "{file_path}" is not encoded in valid UTF-8. Technical details:\n\n{e}'
            error_message = f'File "{file_path}" không đúng mã hóa UTF-8. Chi tiết:\n\n{e}'
        except Exception as e:
            #error_message = f'An error occurred in reading the quiz file. Technical details:\n\n{e}'
            error_message = f'Lỗi đọc file quiz. Chi tiết:\n\n{e}'
        if error_message:
            run_message_text.delete(1.0, tk.END)
            run_message_text.insert(tk.INSERT, error_message)
            run_message_text['fg'] = 'red'
            return
        cwd = pathlib.Path.cwd()
        os.chdir(file_path.parent)
        try:

            #md_file_name = sys.argv[1]

            #md_file = open(md_file_name, 'r')
            #md_script = md_file.read()

            quiz = parse_file(text)
            

            if quiz:
                quiz.export_xml_to_file(file_name)
                #print("XML file(s) successfully generated!")
        except TransitionError as e:
            #error_message = f'Expecting answer, question or header: {e}'
            error_message = f'Cần một câu trả lời, câu hỏi hoặc tiêu đề: {e}'
        except QuizError as e:
            #error_message = f'Quiz error: {e}'
            error_message = f'Quiz lỗi: {e}'
        except Exception as e:
            #error_message = f'Quiz creation failed unexpectedly. Technical details:\n\n{e}'
            error_message = f'Tạo quiz lỗi. Chi tiết:\n\n{e}'
        finally:
            os.chdir(cwd)

        if error_message != None:
            run_message_text.delete(1.0, tk.END)
            run_message_text.insert(tk.INSERT, error_message)
            run_message_text['fg'] = 'red'
        else:
            run_message_text.delete(1.0, tk.END)
            #run_message_text.insert(tk.INSERT, f'Completed! Moodle XML file(s) was created in "{file_path.parent.as_posix()}"')
            run_message_text.insert(tk.INSERT, f'Hoàn thành chuyển đổi sang định dạng Moodle XML. Xem trong thư mục "{file_path.parent.as_posix()}"')
            run_message_text['fg'] = TEXT_FG
    run_button = tk.Button(
        window,
        text='Convert',
        font=(None, 14),
        bg = BUTTON_BG,
        fg = 'white',
        command=run,
    )
    run_button.grid(
        row=current_row, column=0, columnspan=4, padx=(50, 50), pady=(10, 30),
        sticky='nsew',
    )
    current_row += 1


    run_message_label = tk.Label(
        window,
        text='Kết quả:',
        #relief='ridge',
        width=100,
        fg = TEXT_FG,
        bg= LIGHT_BG,
        anchor='w'
    )
    run_message_label.grid(
        row=current_row, column=0, columnspan=column_count, padx=(50, 50), pady=(0, 0),
        sticky='nsew',
    )
    current_row += 1


    run_message_frame = tk.Frame(
        window,
        width=100, height=10,
        borderwidth=1, relief='sunken', bg='white',
    )
    run_message_frame.grid(
        row=current_row, column=0, columnspan=column_count, padx=(50, 50), pady=(10, 10),
        sticky='nsew',
    )
    
    run_message_scrollbar = tk.Scrollbar(run_message_frame)
    run_message_scrollbar.pack(
        side='right', fill='y',
    )
    
    run_message_text = tk.Text(
        run_message_frame,
        height=10, borderwidth=0, highlightthickness=0,
        wrap='word',
        yscrollcommand=run_message_scrollbar.set,
    )
    run_message_text.insert(tk.INSERT, '')
    run_message_text['fg'] = 'gray'
    #run_message_scrollbar.config(command=run_message_text.yview)
    run_message_text.pack(
        side='left', fill='both', expand=False,
        padx=(5, 5), pady=(5, 5),
    )


    window.mainloop()

##
# Regex helpers

def is_header(string):
    return False if get_header(string) is None else True

def is_question(string):
    return False if get_question(string) is None else True

def is_answer(string):
    return is_correct_answer(string) or is_wrong_answer(string)

def is_correct_answer(string):
    return False if get_correct_answer(string) is None else True

def is_wrong_answer(string):
    return False if get_wrong_answer(string) is None else True

def is_blank(string):
    return re.match(EMPTY_LINE_PATTERN, string)

def is_blockcode(string):
    return re.match(BLOCKCODE_PATTERN, string)

def is_eof(string):
    return string == "EOF"

## 
# REGEX matching  and grouping

def get_header(string):
    match = re.match(HEADER_PATTERN, string)
    if match:
        return match.group(1)
    return None

def get_question(string):
    match = re.match(QUESTION_PATTERN, string)
    if match:
        return match.group(3)
    return None


def get_correct_answer(string):
    match = re.match(CORRECT_ANSWER_PATTERN, string)
    if match:
        return match.group(3)
    return None


def get_wrong_answer(string):
    match = re.match(WRONG_ANSWER_PATTERN, string)
    if match:
        return match.group(3)
    return None

##
# REGEX and XML/HTML text transformations

def wrap_cdata(content):
    """Wraps content inside a CDATA xml block."""
    return '<![CDATA[' + content + ']]>'

def sanitize_entities(text):
    """Converts <, >, * and & to html entities."""

    text = text.replace('#','\\#')
    #unfortunately, this order is important
    text = text.replace('&','&amp;')
    text = text.replace('>','&gt;')
    text = text.replace('<','&lt;')
    text = text.replace('*','&ast;')    
        
    return text

def render_answer(text):
    """Replaces any allowed contents, e.g., text, inline code and formulas
     and returns the CDATA content."""

    text = re.sub(SINGLE_LINE_CODE_PATTERN, replace_single_line_code, text)#Thinh
    text = re.sub(SINGLE_DOLLAR_LATEX_PATTERN, replace_latex, text)#Thinh

    return wrap_cdata( markdown( text ) ) 

def render_question(text, md_dir_path):
    """Replaces any allowed contents, e.g., code and images
     and returns the CDATA content."""

    text = re.sub(MULTI_LINE_CODE_PATTERN, replace_multi_line_code, text) #Thinh
    text = re.sub(SINGLE_LINE_CODE_PATTERN, replace_single_line_code, text)
    text = re.sub(IMAGE_PATTERN, replace_image_wrapper(md_dir_path), text)
    text = re.sub(DOUBLE_DOLLAR_LATEX_PATTERN, replace_latex_double_dollars, text)
    text = re.sub(SINGLE_DOLLAR_LATEX_PATTERN, replace_latex, text)
    text = re.sub(TABLE_PATTERN, replace_table, text)
    text = wrap_cdata( markdown_custom(text) )
    return text

def markdown_custom(text):
    """Just calls markdown, but may be extended in the future."""
    return markdown(text)
    
def replace_table(match):
    content = match.group(2)

    html = markdown(content, extensions=['tables'])

    if not CONFIG['table_border']:
        return html

    # Put borders on table. This is not a content issue,
    # but rather a presentation one. However, the rendering
    # is nicer for a quiz environment.
    css_style = """
        <style type="text/css">
            div.border_table + table, th, td {
            border: 1px solid black;
            border-collapse: collapse;
            }
        </style>"""

    return css_style + r"<div class='border_table'>" + html + r"</div>"


def replace_latex_double_dollars(match):
    # Take the part without the $$ at the beginning and at the end
    code = match.group(1)

    # Replace \\ by \\\\ in code
    code = code.replace(r"\\", r"\\\\ ")

    # Replace '\{' by '\\{' and '\}' by '\\}'
    # This must be done after the previous replacement.
    code = code.replace(r'\{', r'\\{')
    code = code.replace(r'\}', r'\\}')

    # Remove unnecessary spaces and new lines in order to have \[math_formula\]
    return "\n \\\\[" +  code.strip() + "\\\\] \n"


def replace_latex(match):
    code = match.group(1)
    code = code.replace('(', r'\left(')
    code = code.replace(')', r'\right)')
    return r'\\(' + code + r'\\)'

def replace_single_line_code(match):
    """
    Produces the output for an inline markdown code bock.

    Output should only be wrapped inside a <code> tag.
    """
    code = match.group(1)
    code = sanitize_entities(code)

    return '<code>' + code + '</code>'


def replace_multi_line_code(match):
    lexer = match.group(1)
    code = match.group(2)

    if not lexer:
        lexer = ''
    
    to_image = True if lexer.find('{img}') > 0 else False

    if to_image:
        lexer = lexer.replace('{img}', '')
        return convert_code_image_base64(lexer, code)
    else:
        #sanitize entities before any conversion to XML
        code = sanitize_entities(code)
        return '<pre><code>' + code + '</code></pre>'


def replace_image_wrapper(md_dir_path):
    def replace_image(match):
        file_name = match.group(1)
        if (not os.path.isabs(file_name)) and ('://' not in file_name):
            file_name = os.path.join(md_dir_path, file_name)
        return build_image_tag(file_name)
    return replace_image


def build_image_tag(file_name):
    extension = file_name.split('.')[-1]
    try:
        data = urlopen(file_name).read()
    except Exception:
        f = open(file_name, 'rb')
        data = f.read()
    base64_image = (base64.b64encode(data)).decode('utf-8')
    src_part = 'data:image/' + extension + ';base64,' + base64_image
    return '<img style="display:block;" src="' + src_part + '" />'

def convert_code_image_base64(lexer_name, code):
    """Converts a code snippet to an image in base64 format."""
    
    from pygments import highlight
    from pygments.lexers import get_lexer_by_name
    from pygments.formatters import ImageFormatter
    from pygments.lexers import ClassNotFound
    import tempfile

    if not lexer_name:
        lexer_name = 'pascal'
    try:
        lexer = get_lexer_by_name(lexer_name)
    except ClassNotFound:
        lexer = get_lexer_by_name('pascal')

    imgBytes = highlight(code, lexer,\
                        ImageFormatter(font_size=CONFIG['pygments.font_size'],\
                            line_numbers = CONFIG['pygments.line_numbers']))

    if CONFIG['pygments.dump_image']:
        img_id = CONFIG['pygments.dump_image_id']

        imgFile = './' + str(img_id) + '.png'
        with open(imgFile, 'wb') as imageOut:
            imageOut.write(imgBytes)
        
        img_id += 1
        CONFIG['pygments.dump_image_id'] = img_id

    temp = tempfile.NamedTemporaryFile()
    temp.write(imgBytes)
    temp.seek(0)

    extension = 'png'
    base64_image = (base64.b64encode(temp.read())).decode('utf-8')
    src_part = 'data:image/' + extension + ';base64,' + base64_image
    
    temp.close()
    return '<img style="display:block;" src="' + src_part + '" />'


######################################################################
# Section 2 - Quiz class, helper functions and constants
######################################################################

class QuizError(Exception):
    pass

class Quiz(dict):
    def __init__(self, *args, default=None, **kwargs):
        super().__init__(*args, **kwargs)
        
        self.section = [] 
        self.current_question = {}

        self.is_valid = False

    def consume_header(self, line):
        """Starts a new section with this header."""

        self.section = []
        self[get_header(line)] = self.section

    def consume_question(self, line):
        """Starts a new question with this content."""

        self.current_question = {'text': get_question(line), 'answers': []}
        self.section.append(self.current_question)

    def append_to_question(self, line): 
        """Appends content to current question."""

        #TODO: there's a problem enforcing line breaks in the output
        self.current_question['text'] += line + '\n'

    def consume_answer(self, line):
        """Appends the answer from this content to the current question."""

        if is_correct_answer(line):

            current_answer = {
                'text': get_correct_answer(line),
                'correct': True
                }
            
            self.current_question['answers'].append(current_answer)

        elif is_wrong_answer(line):

            current_answer = {
                'text': get_wrong_answer(line),
                'correct': False
                }
            
            self.current_question['answers'].append(current_answer)

        else:
            #some other content, ignore.
            pass

    def current_question_has_correct_answers(self):
        correct_answers = [x for x in self.current_question['answers'] if x['correct']]
        correct_answer_count = len(correct_answers)
        
        return (correct_answer_count >= 1)

    def validate(self):
        """Must call after successful parse of document."""
        self.__complete()
        self.is_valid = True        

    def __complete(self):
        """Completes parsed information with 'fraction' values for answers."""

        for key in self:
            section = self[key]
            for question in section:
                correct_answers = [x for x in question['answers'] if x['correct']]
                correct_answer_count = len(correct_answers)
                
                if correct_answer_count < 1:
                    self.is_valid = False
                    raise QuizError("No correct answer(s) for %s" % (question['text']))

                question['single'] = correct_answer_count == 1
                weight = round(100.0 / correct_answer_count, 7)
                for answer in question['answers']:
                    if answer['correct']:
                        answer['weight'] = weight
                    else:
                        if question['single']:
                            answer['weight'] = CONFIG['single_answer_penalty_weight'] * -1
                        else:
                            answer['weight'] = 0

    def export_xml_to_file(self, md_file_name):
        """Produces the XML file outputs; one for each specified category in the md file."""
        if self.is_valid:            
            md_dir_path = os.path.dirname(os.path.abspath(md_file_name))
            '''
            for section_caption in self:
                section = self[section_caption]
                xml_file = open(create_output_filename(md_file_name, section_caption), 'w')
                # xml_file.write(section_to_xml(section, md_dir_path))
                # Prettify xml
                tmp = xml.dom.minidom.parseString(section_to_xml(section_caption, section, md_dir_path))
                xml_file.write(tmp.toprettyxml())

                # xml_file.write(section_to_xml(section_caption, section, md_dir_path))
            '''
            import xml.dom.minidom

            for section_caption in self:
                section = self[section_caption]
                output_filename = create_output_filename(md_file_name, section_caption)
                with open(output_filename, 'w', encoding='utf-8') as xml_file:
                    # Prettify xml
                    tmp = xml.dom.minidom.parseString(section_to_xml(section_caption, section, md_dir_path))
                    xml_file.write(tmp.toprettyxml())

        else:
            #print("Quiz is not marked as valid for export.")
            #raise Exception("Quiz is not marked as valid for export.")
            raise Exception("Quiz không hợp lệ để tạo")

    def export_xml_to_string(self, md_file_name):
        """Produces the XML output and returns the resulting text."""
        if self.is_valid:
            md_dir_path = os.getcwd()
            result = {}            
            for section_caption in self:
                section = self[section_caption]
                result[section_caption] = section_to_xml(section_caption, section, md_dir_path)
            return json.dumps(result, indent=2)
        else:
            #print("Quiz is not marked as valid for export.")
            #raise Exception("Quiz is not marked as valid for export.")
            raise Exception("Quiz không hợp lệ để tạo")
            return ""
        
        
def create_output_filename(md_file_name, section_caption):
    """Generates and sanitizes .xml output filename.

    - All extensions and spaces are removed;
    - Forward slashes '/' (possible in section caption for sub-categories)
        are replaced with hyphens.
    """

    section_caption = section_caption.replace('/','-').replace(' ','')
    md_name = md_file_name.replace('.md','')

    output_file_name = md_name + '_' + section_caption + '.xml'

    return output_file_name

def section_to_xml(section_caption, section, md_dir_path):
    """Convert a parsed section to XML

    Keyword arguments:
    section_caption -- Title of section (used to assign category)
    section -- dictionary mapped content from 'md_script_to_dictionary'
    md_dir_path -- path of the markdown file
    """

    xml = '<?xml version="1.0" ?><quiz>'
    
    #create dummy question to specify category for questions
    xml += '<question type="category"><category><text>' + section_caption + '</text></category></question>'
    
    #add parsed questions
    for index, question in enumerate(section):
        xml += question_to_xml(question, index, md_dir_path)
    xml += '</quiz>'
    return xml


def question_to_xml(question, index, md_dir_path):
    """
    Converts a parsed question to XML.

    <name> is automatically generated from a hash (question text + rand)
    <single> is derived from correct answers (1/0)
    <questiontext> is encoded in CDATA and html format
    """

    #convert question text to CDATA html
    rendered_question_text = render_question(question['text'], md_dir_path)

    #index_part = str(index + 1).rjust(4, '0')
    index_part = str(index + 1).rjust(3, '0')
    q_part = (question['text'] + str(random.random())).encode('utf-8')
    question_single_status = ('true' if question['single'] else 'false')
    
    xml = '<question type="multichoice">'
    # question name
    xml += '<name><text>'
    #xml += index_part + hashlib.md5(q_part).hexdigest()
    xml += 'Question '+ index_part + '_'+ hashlib.md5(q_part).hexdigest()
    xml += '</text></name>'
    # question text
    xml += '<questiontext format="html"><text>'
    xml += rendered_question_text
    xml += '</text></questiontext>'
    # answer
    for answer in question['answers']:
        xml += answer_to_xml(answer)
    
    # other properties
    xml += '<shuffleanswers>' + CONFIG['shuffle_answers'] + '</shuffleanswers>'
    xml += '<single>' + question_single_status + '</single>'
    xml += '<answernumbering>' + CONFIG['answer_numbering'] + '</answernumbering>'
    xml += '</question>'
    return xml


def answer_to_xml(answer):
    """Produces the XML output for an answer."""

    text = answer['text']

    #make any necessary transformatins to answer
    text = render_answer(text)

    xml = '<answer fraction="'+str(answer['weight'])+'">'
    xml += '<text>'+text+'</text>'
    xml += '</answer>'
    return xml


######################################################################
# Section 3 - FSM implementation
######################################################################

class InitializationError(Exception):
    """Signals that the FSM is not properly configured to run."""
    pass

class TransitionError(Exception):
    """Signals that a transition forced by the parsing is not valid."""
    pass

class StateMachine:
    """
    Provides the definition of a finite state machine in python that 
    enables to change state and run a parsed line within that state,
    i.e., the FSM will run a delegate function according to its current
    state.
    """
    def __init__(self):
        self.handlers = {}
        self.state = None
        self.endStates = []

    def add_state(self, name, handler, end_state=0):
        """Adds a state (name) and its handler function."""

        name = name.upper()
        self.handlers[name] = handler
        if end_state:
            self.endStates.append(name)

    def set_start(self, name):
        """Sets the start state (name).
        The state must have been previously added through 'add_state' method. 
        """
        self.state = name.upper()

    def run(self, quest, line_text, line_number):
        """Executes the handler for the current state."""

        try:
            handler = self.handlers[self.state]
        except:
            raise InitializationError("must call .set_start() before .run()")
        if not self.endStates:
            raise  InitializationError("at least one state must be an end_state")
    
        if CONFIG['debug']:
            print("In state %25s | Processing: %s" %(self.state, line_text))
        
        newState = handler(quest, line_text, line_number)
        self.state = newState.upper()

        if self.state in self.endStates and CONFIG['debug']:
            print("Success! Reached an end state:", newState)



######################################################################
# Section 4 - FSM Markdown Parser
######################################################################

##
# FSM State handlers - These implement the transitions and their actions
#
# Each handler receives the current quiz, the currently parsed line
# line number. Line numbers aren't currently used within each state,
# but may be useful in the future for some reason.

def state_start(quiz, line_text, line_number):
    
    if is_blank(line_text):
        state = "start"
    elif is_header(line_text):
        quiz.consume_header(line_text)
        state = "parse_header"
    elif is_question(line_text):
        quiz.consume_question(line_text)
        state = "parse_question"
    else:
        #raise TransitionError("Expecting a header or a question")
        raise TransitionError("Cần một tiêu đề hoặc một câu hỏi")

    return state

def state_parse_header(quiz, line_text, line_number):
    
    if is_blank(line_text):
        # do nothing
        state = "parse_header"
    elif is_question(line_text):
        quiz.consume_question(line_text)
        state = "parse_question"
    else:
        #raise TransitionError("Expecting a question")
        raise TransitionError("Cần một câu hỏi")

    return state

def state_parse_question(quiz, line_text, line_number):

    if is_blank(line_text):
        # do nothing
        state = "parse_question"
    elif is_blockcode(line_text):
        quiz.append_to_question(line_text)
        state = "parse_question_codeblock"
    elif is_answer(line_text):
        quiz.consume_answer(line_text)
        state = "parse_answer"
    elif is_header(line_text) or is_question(line_text) or is_eof(line_text):
        #raise TransitionError("Expecting text, codeblock or answer")
        raise TransitionError("Cần text, code công thức hoặc câu trả lời")
    else:
        quiz.append_to_question(line_text)
        state  = "parse_question"
        pass

    return state

def state_parse_question_codeblock(quiz, line_text, line_number):

    # In a codeblock we accept everything until it closes
    if is_eof(line_text):
        #raise TransitionError("Expecting closing codeblock")
        raise TransitionError("Cần ký tự đóng code công thức")
    elif is_blockcode(line_text):
        quiz.append_to_question(line_text)
        state = "parse_question"
    else:
        quiz.append_to_question(line_text)
        state = "parse_question_codeblock"

    return state

def state_parse_answer(quiz, line_text, line_number):

    if is_blank(line_text):
        # do nothing
        state = "parse_answer"
    elif is_answer(line_text):
        quiz.consume_answer(line_text)
        state = "parse_answer"
    elif is_question(line_text):
        if quiz.current_question_has_correct_answers():
            quiz.consume_question(line_text)
            state = "parse_question"
        else:
            #raise TransitionError("Expecting at least one correct answer in previous question")
            raise TransitionError("Cần ít nhất một đáp án đúng trong câu hỏi trước")
    elif is_header(line_text):
        if quiz.current_question_has_correct_answers():
            quiz.consume_header(line_text)
            state = "parse_header"
        else:
            #raise TransitionError("Expecting at least one correct answer in previous question")
            raise TransitionError("Cần ít nhất một đáp án đúng trong câu hỏi trước")
    elif is_eof(line_text):
        if quiz.current_question_has_correct_answers():
            # mark as valid and go to end state
            quiz.validate()
            state = "end"
        else:
            #raise TransitionError("Expecting at least one correct answer in previous question")
            raise TransitionError("Cần ít nhất một đáp án đúng trong câu hỏi trước")
    else:
        #raise TransitionError("Expecting answer, question or header")
        raise TransitionError("Cần một câu trả lời, câu hỏi hoặc tiêu đề")

    return state

def state_end(quiz, line_text, line_number):
    """End state."""
    pass
    
##
# The Parser loop

def parse_file(md_script):
    """
    Parses the markdown file one line at a time and returns a Quiz

    :param md_script: list of file lines
	:type md_script: list
    """
    global error_message
    # Create Quiz
    quiz = Quiz()

    # Initialize state machine
    
    
    m = StateMachine()
    m.add_state("start", state_start)
    m.add_state("parse_header", state_parse_header)
    m.add_state("parse_question", state_parse_question)
    m.add_state("parse_answer", state_parse_answer)
    m.add_state("parse_question_codeblock", state_parse_question_codeblock)
    m.add_state("end", state_end, end_state=1)
    m.set_start("start")
    
    # Parse file lines
    md_lines = md_script.split(NEW_LINE)
    md_lines.append("EOF")
    line_number = 1
    try:
        for md_row in md_lines:
            md_row = md_row.rstrip('\r')
            md_row = md_row.rstrip('\n')
            
            m.run(quiz, md_row, line_number)

            line_number += 1
        
    except TransitionError as e:
        #print("Error at line %d: %s." % (line_number, e))
        #error_message = r"Error in quiz file at line %d: %s." % (line_number, e)
        error_message = r"Lỗi trong file quiz tại dòng %d: %s." % (line_number, e)
        quiz = None

    return quiz

######################################################################
# Section 5 - Main
######################################################################

if __name__ == '__main__':
    main()
