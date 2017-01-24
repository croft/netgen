
if [[ -n $BASH_VERSION ]]; then
  SOURCE="${BASH_SOURCE[0]}"
elif [[ -n $ZSH_VERSION ]]; then
  SOURCE="${(%):-%N}"
else
  echo "Shell not supported"
  return
fi

# See http://stackoverflow.com/questions/59895/can-a-bash-script-tell-what-directory-its-stored-in
while [ -h "$SOURCE" ]; do
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ $SOURCE != /* ]] && SOURCE="$DIR/$SOURCE"
done

_TOP=$(dirname $(dirname "$( cd -P "$( dirname "$SOURCE" )" && pwd )"))

export LOGICBLOX_HOME=$_TOP
export LB_MODELER_HOME=$LOGICBLOX_HOME
export LB_WEBSERVER_HOME=$_TOP
export LB_WEBCLIENT_HOME=$_TOP
export LB_MEASURE_SERVICE_HOME=$_TOP/libexec/logicblox/measure-service
export S3LIB_HOME=$_TOP
export LB_WORKFLOW_HOME=$_TOP
export LAYERBLOX_HOME=$_TOP/libexec/logicblox/layerblox
export LB_WORKBOOK_SERVICE_HOME=$_TOP

export PATH=$LOGICBLOX_HOME/bin:$LB_WORKFLOW_HOME/bin:$PATH
export LB_LIBRARY_PATH=$LOGICBLOX_HOME/share:$LB_MEASURE_SERVICE_HOME/share:$LB_LIBRARY_PATH
if [[ -f $LOGICBLOX_HOME/libexec/python-argcomplete.sh ]]; then
  source $LOGICBLOX_HOME/libexec/python-argcomplete.sh
fi
