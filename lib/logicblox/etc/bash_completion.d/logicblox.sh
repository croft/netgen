# Copyright 2012-2013, Andrey Kislyuk and argcomplete contributors.
# Licensed under the Apache License. See https://github.com/kislyuk/argcomplete for more info.

_lb_argcomplete() {

        local IFS=$(echo -e '\v')
        COMPREPLY=( $(_ARGCOMPLETE_IFS="$IFS" \
            COMP_LINE="$COMP_LINE" \
            COMP_POINT="$COMP_POINT" \
            _ARGCOMPLETE_COMP_WORDBREAKS="$COMP_WORDBREAKS" \
            _ARGCOMPLETE=$ARGCOMPLETE \
            "$1" 8>&1 9>&2) )

        if [[ $? != 0 ]]; then
            unset COMPREPLY
        fi

}
complete -o filenames -F _lb_argcomplete lb
