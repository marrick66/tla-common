#!/usr/bin/env python3

import argparse
import pathlib
import os
import sys
import subprocess

parser = argparse.ArgumentParser(description='tlc wrapper')
parser.add_argument('module', type=str, help='the module to check')
args = parser.parse_args()

root = os.getcwd()
libraries = []
modules = {}
toolbox_path = os.environ['TLA_TOOLBOX_PATH']

if len(toolbox_path) == 0:
    print("No toolbox path defined.")
    sys.exit()

tla_java_opts = ''

for file in pathlib.Path(root).rglob('*.tla'):
    lib = os.path.dirname(file)
    if not lib in libraries:
        libraries.append(lib)
        tla_java_opts += lib + ':'

for file in pathlib.Path(root).rglob('*.cfg'):
    mod = os.path.basename(file)[:-4]
    modules[mod] = os.path.dirname(file)

module_path = pathlib.Path(os.path.abspath(args.module))
module_parent = module_path.parent
module_name = module_path.name
cmd = f'java -cp {toolbox_path}:{tla_java_opts} tlc2.TLC -dump dot output.dot {module_name}'

print(os.environ["CLASSPATH"])
print(cmd)
os.chdir(module_parent)
os.system(cmd)