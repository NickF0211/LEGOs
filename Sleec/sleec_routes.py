import base64
import os
from flask import Flask, request, send_file
from flask_cors import CORS
import json
import subprocess
import shutil
from sleecParser import check_input_red, check_input_conflict
# import signal
#
# def handler(signum, frame):
#     raise TimeoutError()
#
# signal.signal(signal.SIGABRT, handler)
SLEEC_template = "def_start\n{definitions}\ndef_end\nrule_start\n{rules}\nrule_end"
# SLEEC_template = "def_start\n{definitions}\ndef_end\nrule_start\n{rules}\nrule_end\nconcern_start\n{concerns}\nconcern_end"

def str2bool(v):
    if isinstance(v, bool):
        return  v
    if v.lower() in ("yes", "true", "t", "1"):
        return "True"
    else:
        return "False"

app = Flask(__name__)
CORS(app)
TIMEOUT = 3000
@app.route("/compiler",methods=["POST"])
def get_query_from_react():
    data = request.get_json()
    content = data["body"]
    # print(content)
    editor_input = json.loads(content)    #now parse the first editor results:
    src_loc = os.path.dirname(os.path.abspath(__file__))
    definitions = ""
    rules = ""
    concerns = ""
    for key, value in editor_input.items():
        filename = get_translated_filename(key)
        if filename is None:
            print ("{} : {}".format(key, value))
        else:

            if filename == "definitions":
                definitions = base64.b64decode(bytes(value, 'utf-8')).decode('utf-8')
            elif filename == "rules":
                rules = base64.b64decode(bytes(value, 'utf-8')).decode('utf-8')
            # elif filename == "concerns":
            #     concerns = base64.b64decode(bytes(value, 'utf-8')).decode('utf-8')
    try:
        # signal.alarm(TIMEOUT)
        model_str = SLEEC_template.format(concerns = concerns, rules = rules, definitions=definitions)
        if editor_input['type'] == "Conflict":
            result = check_input_conflict(model_str, multi_entry=True)
        elif editor_input['type'] == "Redundancies":
            result = check_input_red(model_str, multi_entry=True)
        else:
            result = "Error: Not a valid command"

        output = result
    except TimeoutError:
        output = "TIMEOUT: {}".format(str(TIMEOUT))

    if isinstance(output, str):
        return output
    else:
        return prepare_output(output)

def prepare_output(result_tuple):
    results = []
    if isinstance(result_tuple, list):
        for ret_str, hls in result_tuple:
            new_hls = [[a, b] for a, b in hls]
            results.append({"resValue":ret_str, "highligedIndexes": new_hls})
        return {"result":results}
    else:
        ret_code, ret_str, hls = result_tuple
        new_hls = [[a, b] for a, b in hls]
        return {"resValue":ret_str, "highligedIndexes": new_hls}



def get_translated_filename(key):
    if key == "firstEditorInput":
        return "definitions"
    elif key == "secondEditorInput":
        return "rules"
    elif key == "thirdEditorInput":
        return "concerns"
    else:
        return None

if __name__ == '__main__':
    app.run()