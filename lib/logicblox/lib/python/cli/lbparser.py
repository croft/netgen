import sys
import argparse
import lb_exception

def set_formatter(subparsers):
    for sp in subparsers:
        sp.formatter_class = CLICommandHelpFormatter
        set_formatter(list_subparsers(sp))

def list_subparsers(parser):
    if parser._subparsers is not None:
        for group in parser._subparsers._group_actions:
            for sub_command, sub_parser in group.choices.items():
                yield sub_parser
                for sp in list_subparsers(sub_parser):
                    yield sp

class CLICommandHelpFormatter(argparse.HelpFormatter):
    """
        A help formatter that sorts commands and avoids listing the commands.
    """

    def _fill_text(self, text, width, indent):
        """
            overriding method used to format long description text
            to allow preformatted descriptions
        """
        if(text.startswith('RAW')):
           return text[4:]
        return argparse.HelpFormatter._fill_text(self, text, width, indent)
    def _iter_indented_subactions(self, action):
        """
            Override this method to sort the commands according to our _sort_commands
            function, which will first show db commands, and then the rest.
        """
        try:

            subactions_func = action._get_subactions

        except AttributeError:
            pass

        else:
            self._indent()
            if isinstance(action, argparse._SubParsersAction):
                for subaction in self._sort_commands(subactions_func()):
                    yield subaction
            else:
                for subaction in subactions_func():
                    yield subaction
            self._dedent()

    def _sort_commands(self, commands):
        """
            A method to sort the commands so that the db commands show first in the list.
        """
        return sorted(commands, key=lambda x: x.dest)

    def _metavar_formatter(self, action, default_metavar):
        """
            Override this method to avoid printing a list of commands, which pollutes the help.
        """
        def format(m):
            if m:
                if action.__class__ != argparse._SubParsersAction._ChoicesPseudoAction:
                    return m.upper().replace('_', '-')
                else:
                    return m

        if action.metavar is not None:
            result = format(action.metavar)
        elif action.choices is not None:
            # This method is a clone of the super method except for this branch. Here we
            # sort the choice_strs so that the list at least is sorted. But in the end
            # it looks nicer if we just remove the whole list if choices are for subcommands.
            if action.__class__ == argparse._SubParsersAction:
                result = ''
            else:
                choice_strs = sorted([str(choice) for choice in action.choices])
                result = '{%s}' % ','.join(choice_strs)
        else:
            result = format(default_metavar)

        def format(tuple_size):
            if isinstance(result, tuple):
                return result
            else:
                return (result, ) * tuple_size
        return format

class LBArgumentParser(argparse.ArgumentParser):
    """
    An ArgumentParser which throws an exception when failing instead of calling System.exit, and provides 
    additional info in the usage message.
    """

    # these strings must be in fields because the documentation generator also needs access to them
    title = 'LogicBlox command line interface'
    extra_usage = '''

usage: lb 
           start lb interactive

usage: lb FILE1.lb [ FILE2.lb ... ]
           interpret the scripts FILE1.lb, FILE2.lb sequentially
           NOTE: script files MUST have a .lb suffix

'''

    def error(self, message):
        raise lb_exception.ArgumentParserError(message)


    def print_help(self, file=None):

        if file is None:
            file = sys.stdout

        message = self.format_help()
        if self.prog=="lb":
            message = self.title + self.extra_usage + message

        self._print_message(message, file)



class LBHelpFormatter(CLICommandHelpFormatter):
    """
        A help formatter that sorts the commands in the list and shows a separated section for
        db commands versus other commands.
    """

    def __init__(self,
                 prog,
                 indent_increment=2,
                 max_help_position=24,
                 width=None):
        """
            Call super and then keep a list of the db commands to be used later.
        """
        super(LBHelpFormatter, self).__init__(prog, indent_increment, max_help_position, width)

        def get_db_commands_list():
            try:
                from cli.command import db
                return db.get_db_commands_list()
            except:
                return []

        # a list of db commands
        self.db_commands = get_db_commands_list()
        # whether we are formatting db or other commands
        self.formatting_db = True

    def _sort_commands(self, commands):
        """
            A method to sort the commands so that the db commands show first in the list.
        """
        # a function that prepends '_' to db commands during comparison.
        def sort_commands(x):
            if x.dest in self.db_commands:
                return '_' + x.dest
            return x.dest

        return sorted(commands, key=sort_commands)

    def _format_action(self, action):
        """
            Override the formatting of a command. Here we maintain the formatting_db flag
            that indicates whether we moved from the db commands to the other. When we do
            the move, we print an additional header. SUPPRESS indicates that we started
            over again.
        """
        if action.dest == argparse.SUPPRESS:
            self.formatting_db = True

        text = super(LBHelpFormatter, self)._format_action(action)

        if self.formatting_db and not action.dest in self.db_commands:
            text = "\n\nadditional commands:\n\n" + text
            self.formatting_db = False

        return text
