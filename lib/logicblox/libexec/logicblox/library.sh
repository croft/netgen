#!/usr/bin/env bash

# Ensure that `ps' can be found, even in a Nix build.
if [ "$(uname)" = Darwin ]; then
    PATH=$PATH:/bin
fi

########################################################################################
# Printing error messages
#
function infomessage()
{
   echo -e "$(date "+%Y-%m-%d %H:%M:%S%z") - info: $1"
}

function warningmessage()
{
   echo -e "$(date "+%Y-%m-%d %H:%M:%S%z") - warning: $1"
}

function errormessage()
{
   echo -e "$(date "+%Y-%m-%d %H:%M:%S%z") - error: $1"
}

function exit_with_error()
{
   exit 1
}

#########################################################################################
# Sanity checking and initialization
#
if test -z "$LOGICBLOX_HOME"; then
   errormessage "LOGICBLOX_HOME is not set"
   exit 1
fi

if test -z "$LB_DEPLOYMENT_HOME"; then
   export LB_DEPLOYMENT_HOME="$HOME/lb_deployment"
fi

if test -z "$LB_LOGDIR"; then
   LB_LOGDIR="$LB_DEPLOYMENT_HOME/logs"
fi

if test -z "$LB_BLOXOPTDIR"; then
   LB_BLOXOPTDIR="$LB_DEPLOYMENT_HOME/bloxopt/"
fi


# Note: LB_SERVER_DATA_DIR is not a standard environment variable. The
# setting should really be taken from lb-server.config, but this file
# is not trivial to parse. It is necessary to make the directory here,
# because lb-server does not create the directory if it does not exist.
if test -z "$LB_SERVER_DATA_DIR"; then
   LB_SERVER_DATA_DIR="$LB_DEPLOYMENT_HOME/workspaces"

   if test ! -e "$LB_SERVER_DATA_DIR"; then
      mkdir -p "$LB_SERVER_DATA_DIR"
   fi
fi

if test -z "$CRONLOG"; then
  CRONLOG=/var/log/cron
fi

export LB_BLOXCOMPILER_SERVER="true"

mkdir -p $LB_LOGDIR/current

mkdir -p $LB_BLOXOPTDIR

#########################################################################################
# Get configuration settings

function get_config()
{
   local service=$1
   local config=$2

   local value=""
   local custom_file="$LB_DEPLOYMENT_HOME/config/$service.config"
   local default_file="$LOGICBLOX_HOME/config/$service.config"

   if test "$service" = "lb-web-server"; then
     local default_file="$LB_WEBSERVER_HOME/config/lb-web-server.config"
   fi

   if test -e $custom_file; then
     value="$(sed -n "s/^[ \t]*$config *= *\([^ ]*.*\)/\1/p" $custom_file)"
   fi

   if test -z "$value"; then
      if test -e $default_file; then
         value="$(sed -n "s/^[ \t]*$config *= *\([^ ]*.*\)/\1/p" $default_file)"
      fi
   fi

   if test -z "$value"; then
      errormessage "required configuration setting $config not found for service $1"
      exit_with_error
   fi

   for var in HOME LOGICBLOX_HOME LB_DEPLOYMENT_HOME LB_LOGDIR; do
      value="$(echo $value | sed 's%$('"$var"')%'$(eval echo "\$$var")'%g')"
   done

   echo "$value"
}

#########################################################################################
# Checking for running processes
#
function print_services()
{
  local method=$1

  if [[ "$method" == "heuristic" ]] ; then
    # print services by heuristic

    local heuristic="bin/lb-server|lb-compiler.jar|com.logicblox.bloxweb.Main|dlb-server"

    procs="$(ps -fwww -u $(id -un) | egrep $heuristic | grep -v grep)"
    if [ -z "$procs" ]; then
      infomessage "no running services by heuristic on command-line"
    else
        infomessage "currently running services by heuristic on command-line:"
        echo
        ps -fwww -u $(id -un) | egrep $heuristic | grep -v grep | awk '{print "   " $0}'
        echo
    fi

  elif [[ "$method" == "check" ]] ; then
    infomessage "currently running services by status check:"
    echo -n "   " >&2 && check_and_fail "lb-compiler-server" check_lbcompiler > /dev/null
    echo -n "   " >&2 && check_and_fail "lb-server" check_lb_server > /dev/null
    echo -n "   " >&2 && check_and_fail "lb-web-server" check_web_server > /dev/null

  else
    # print services by PIDs stored in LB_LOGDIR

    local procs=`ls $LB_LOGDIR/current/*.pid 2> /dev/null`

    if [ -z "$procs" ]; then
      infomessage "no running services by .pid files (no .pid files exist)"
    else
      infomessage "currently running services by .pid files:"
     
      local error_msgs
      echo
      for pid_file in $procs; do
        pid=`cat $pid_file`
        proc="`ps -fwww -p $pid`"
        if [ $? -eq "0" ]; then
          echo "$proc" | tail -n 1 | awk '{print "   " $0}'
        else
          error_msgs="Removing inactive process file $pid_file\n$error_msgs"
          rm $pid_file
        fi
      done
      echo -e "\n$error_msgs" | awk '{print "   " $0}'

    fi
  fi
}

function check_cmd() {
   local cmd=$1
   $cmd &> /dev/null
   if [[ "$?" == "0" ]] ; then
     echo 1
   fi
}

function check_lbcompiler()
{
   check_cmd "$LOGICBLOX_HOME/bin/lb compiler-server status"
}

function check_web_server()
{
   check_cmd "$LOGICBLOX_HOME/bin/lb web-server status"
}

function check_lb_server()
{
   check_cmd "$LOGICBLOX_HOME/bin/lb server status"
}

function check_allservices()
{
   check_lbcompiler
   check_lb_server
   check_web_server
}

#########################################################################################
# Waiting for processes to be down
#
function wait_for_shutdown()
{
   local check_function=$1
   local name=$2
   local pause=$3
   local maxWait=$4
   local waiting=0
   local c=1
   while [[ $waiting -lt $maxWait ]]; do
      let waittime=$maxWait-$waiting
      c=$($check_function | wc -l)
      c=$(echo $c)

      if [[ $c == 0 ]]; then
         infomessage "service '$name' has stopped"
         break
      else
         infomessage "waiting for service '$name' to stop ($waittime seconds remaining)"
      fi
      sleep $pause
      let waiting=$waiting+$pause
   done
}

function wait_for_lbcompiler()
{
   wait_for_shutdown check_lbcompiler "lb-compiler" 1 30
}

function wait_for_web_server()
{
   wait_for_shutdown check_web_server "lb-web-server" 1 30
}

function wait_for_lb_server()
{
   wait_for_shutdown check_lb_server "lb-server" 1 120
}

function ensure_services_shutdown()
{
   allservices=$(check_allservices)
   if [[ -n $allservices ]]; then
      errormessage "some services are still running according to status check"
      print_services
      # Temporarily dumping some more info to debug issues
      print_services "heuristic"
      print_services "check"
      exit_with_error
   fi
}

#########################################################################################
# Starting processes (wraps launch)
#
function start_process()
{
   local start_function=$1
   local check_function=$2
   local name=$3
   local maxWait=$4
   local pause="1"

   infomessage "starting service '$name' ..."
   $start_function
   sleep 0.2

   local waiting=0
   local c=1
   local started=""

   while [[ $waiting -lt $maxWait ]]; do
      let waittime=$maxWait-$waiting
      c=$($check_function)

      if [[ ! -z "$c" ]]; then
         infomessage "service '$name' started"
         started="true"
         break
      else
         infomessage "waiting for service '$name' to start ($waittime seconds remaining)"
      fi
      sleep $pause
      let waiting=$waiting+$pause
   done

   local list=$($check_function)
   if [[ -z "$list" ]]; then
      errormessage "service '$name' did not start. Aborting."
      exit_with_error
   else
      if [[ -z "$started" ]]; then
         infomessage "service '$name' started"
      fi
   fi
}

function start_lbcompiler()
{
   start_process launch_lbcompiler check_lbcompiler "lb-compiler" 10
}

function start_web_server()
{
  if test -n "$LB_WEBSERVER_HOME"; then
    local enabled="$(get_config lb-web-server enabled)"

    if test "$enabled" = "true"; then
      # NOTE: this is now handled within Python so we just set it to 1 here
      start_process launch_web_server check_web_server "lb-web-server" 1
    else
      warningmessage "lb-web-server is disabled, will not start lb-web-server"
    fi
  else
    warningmessage "lb-web-server is not available (LB_WEBSERVER_HOME not set), will not start lb-web-server"
  fi
}

function start_lb_server()
{
   start_process launch_lb_server check_lb_server "lb-server" 10
}

function start_all_nrt()
{
   start_lbcompiler
   start_lb_server
   start_web_server
}

#########################################################################################
# Launching processes
#

function launch_lbcompiler()
{
   local jvm_args=$(get_config lb-server jvmServerArgs)
   if [[ $jvm_args =~ 'error: required configuration setting jvmServerArgs' ]]; then
     jvm_args="$(get_config lb-server jvmArgs)"
   fi
   if test -e $LB_LOGDIR/current/lb-compiler.pid; then
      rm $LB_LOGDIR/current/lb-compiler.pid
   fi

   nohup java $jvm_args -Djava.library.path=${LOGICBLOX_HOME}/lib -jar $LOGICBLOX_HOME/share/java/lb-compiler.jar daemonStart > $LB_LOGDIR/current/lb-compiler.log 2>&1 &
   echo $! > $LB_LOGDIR/current/lb-compiler.pid
}

function launch_web_server()
{
   ## this will start lb-web-server in daemon mode and save the pid file in logs/current
   $LOGICBLOX_HOME/bin/lb web-server start --daemonize true
}

function launch_lb_server()
{
   #echo "Original settting: LANG=>>$LANG<<"
   #echo setting LANG=C
   export LANG=C
   $LOGICBLOX_HOME/bin/lb server start
}

#########################################################################################
# Log rotation
#
function logrotate_all()
{
   TODAY=$(date +%Y%m%d_%H%M)
   LOGDIR="$LB_LOGDIR/${TODAY}"
   mkdir -p $LOGDIR

   infomessage "saving current logs in '$LOGDIR'"
   if [ "$(ls -A $LB_LOGDIR/current)" ]; then
      mv $LB_LOGDIR/current/* $LOGDIR/
   fi
}

#########################################################################################
# Shutdown processes
#
#
function shutdown_process()
{
   local shutdown_function=$1
   local wait_function=$2
   local check_function=$3
   local name=$4
   local killoption=$5

   local list=$($check_function)
   if [[ -n "$list" ]]; then
      infomessage "shutting down '$name' ..."
      $shutdown_function
   else
      infomessage "service '$name' is not running"
      return 0
   fi

   $wait_function
   local list=$($check_function)
   if [[ -z "$list" ]]; then
      infomessage "service '$name' successfully terminated"
   else
      for i in $list; do
         warningmessage "service '$name' process '$i' has not stopped.  Using 'kill' to stop it..."
         kill $i
      done

      $wait_function
      local list=$($check_function)
      if [[ -z "$list" ]]; then
         infomessage "'$name' successfully terminated"
      else
         errormessage "'$name' is still running"
         return 1
      fi
   fi

   return 0
}

function shutdown_process_nokill()
{
   local shutdown_function=$1
   local wait_function=$2
   local check_function=$3
   local name=$4

   infomessage "shutting down '$name' ..."

   local list=$($check_function)
   if [[ -n "$list" ]]; then
      $shutdown_function
   else
      infomessage "service '$name' is not running"
      return 0
   fi

   $wait_function
   local list=$($check_function)
   if [[ -z "$list" ]]; then
      infomessage "service '$name' successfully terminated"
   else
      errormessage "'$name' is still running"
      return 1
   fi

   return 0
}


function shutdown_process_wait_only()
{
   local wait_function=$1
   local check_function=$2
   local name=$3

   infomessage "waiting for shutdown of '$name' ..."

   local list=$($check_function)
   if [[ -z "$list" ]]; then
      infomessage "service '$name' is not running"
      return 0
   fi

   $wait_function
   local list=$($check_function)
   if [[ -z "$list" ]]; then
      infomessage "service '$name' successfully terminated"
   else
      errormessage "service '$name' is still running"
      return 1
   fi

   return 0
}

function shutdown_lbcompiler()
{
   shutdown_process shutdown_lbcompiler_helper wait_for_lbcompiler check_lbcompiler "lb-compiler" $1
}

function shutdown_lbcompiler_helper()
{
   if test -e $LB_LOGDIR/current/lb-compiler.pid; then
      local compiler_pid=$(cat $LB_LOGDIR/current/lb-compiler.pid)
      if [[ -z "$compiler_pid" ]]; then
         warningmessage "lb-compiler pid file is empty"
      else
         infomessage "stopping lb-compiler process $compiler_pid"
         kill $compiler_pid && rm -f $LB_LOGDIR/current/lb-compiler.pid
      fi
   else
      warningmessage "lb-compiler does not have expected pid file"
   fi
}

function shutdown_web_server()
{
   shutdown_process shutdown_web_server_helper wait_for_web_server check_web_server "lb-web-server" $1
}

function shutdown_web_server_helper()
{
   $LOGICBLOX_HOME/bin/lb web-server stop
}

function shutdown_lb_server()
{
   shutdown_process \
      shutdown_lb_server_helper \
      wait_for_lb_server \
      check_lb_server \
      "lb-server" \
      $1
}

function shutdown_lb_server_helper()
{
   if test -e $LB_LOGDIR/current/lb-server.pid; then
      local pid=$(cat $LB_LOGDIR/current/lb-server.pid)
      if [[ -z "$pid" ]]; then
         warningmessage "lb-server pid file is empty"
      else
         infomessage "stopping lb-server process $pid"
         $LOGICBLOX_HOME/bin/lb server stop && rm -f $LB_LOGDIR/current/lb-server.pid
      fi
   else
      warningmessage "lb-server does not have expected pid file"
   fi
}

function shutdown_all_nrt()
{
   shutdown_web_server
   if [[ $? -ne 0 ]]; then
      errormessage "lb-web-server was not stopped."
      errormessage "other services will not be stopped"
      exit_with_error
   fi

   shutdown_lb_server
   if [[ $? -ne 0 ]]; then
      errormessage "lb-server was not stopped."
      errormessage "lb-compiler will not be stopped."
      print_services
      exit_with_error
   fi

   shutdown_lbcompiler
   if [[ $? -ne 0 ]]; then
      errormessage "lb-compiler was not stopped."
      print_services
      exit_with_error
   fi
}

#########################################################################################
# Check LB services status
#

function check_and_fail()
{
   local name=$1
   local check=$2
   local failed=0

   format="%-24s : %s\n"
   if [[ -z "$($check)" ]]; then
     printf  "$format" "$name" "failed" >&2
     failed=1
   else
      printf "$format" "$name" "running" >&2
   fi
   echo "$failed"
}

function check_status()
{
   compiler_failed=`check_and_fail "lb-compiler-server" check_lbcompiler`
   lb_failed=`check_and_fail "lb-server" check_lb_server`

   web_server_failed=0
   if test -n "$LB_WEBSERVER_HOME"; then
     # local web_server_enabled="$(get_config web_server enabled)"
     # if test "$web_server_enabled" = "true"; then
       web_server_failed=`check_and_fail "lb-web-server" check_web_server`
     # fi
   fi

   rc="0"
   if [[ "$lb_failed" != "0" || "$compiler_failed" != "0" || "$web_server_failed" != "0" ]]
   then
      rc="1"
   fi
   exit $rc
}


