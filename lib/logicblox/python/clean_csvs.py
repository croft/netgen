import os
import sys
import argparse
import re

csv_filenames = [
    'CompositeAggs.csv',
    'CompositeSpreads.csv',
    'Dimensions.csv',
    'Hierarchies.csv',
    'Intersections.csv',
    'Levels.csv',
    'Measures.csv'
]

# Removes C-style comments from a string
def remove_comments(text):
    def replacer(match):
        s = match.group(0)
        if s.startswith('/'):
            return ""
        else:
            return s
    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE
    )
    return re.sub(pattern, replacer, text)


def remove_blank_lines(text):
    return os.linesep.join([s for s in text.splitlines() if s])

def clean_csvs(csv_filenames,config_dir,csv_dir):
    for csvfile in csv_filenames:
        with open(os.path.join(config_dir,csvfile), 'r') as orig, open(os.path.join(csv_dir, csvfile), 'w') as dest:
            dest.write(remove_blank_lines(remove_comments(orig.read())))

def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument('config_dir')
    parser.add_argument('csv_dir')

    args = parser.parse_args()
    config_dir = args.config_dir
    csv_dir = args.csv_dir

    clean_csvs(csv_filenames,config_dir,csv_dir)

if __name__ == '__main__': main()

