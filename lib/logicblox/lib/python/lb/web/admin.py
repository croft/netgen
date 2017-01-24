import lb.web.service
import lb.web.admin_pb2
import os

class Client(object):

  def __init__(self, host = "localhost", port = "55183", path = "/lb-web/admin"):
      self.client = lb.web.service.Client(host, port, path)

  def install_handlers(self, config):
      request = lb.web.admin_pb2.Request()

      # the path may be coming in as a relative path.  since the working dir
      # of bloxweb may be different, need to convert to absolute path
      request.install_handlers.config = os.path.abspath(config[0])

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.install_handlers.handler

  def install_jar(self, jar):
      '''
        Install the jar located in the file paths defined by the first element
        of the jar list. Note that jar must be a list and only the first one is
        installed. Don't ask me why.
      '''
      request = lb.web.admin_pb2.Request()

      # the path may be coming in as a relative path.  since the working dir
      # of bloxweb may be different, need to convert to absolute path
      request.install_handlers.jar = os.path.abspath(jar[0])

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.install_handlers.handler

  def install_config(self, config):
      request = lb.web.admin_pb2.Request()

      # the path may be coming in as a relative path.  since the working dir
      # of bloxweb may be different, need to convert to absolute path
      request.install_config.config = os.path.abspath(config[0])

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.install_config.handler, response.install_config.workspace

  def install_config_from_jar(self, jar):
      request = lb.web.admin_pb2.Request()

      # the path may be coming in as a relative path.  since the working dir
      # of bloxweb may be different, need to convert to absolute path
      request.install_config.jar = os.path.abspath(jar[0])

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.install_config.handler, response.install_config.workspace

  def status(self):
      request = lb.web.admin_pb2.Request()
      request.status.Clear()
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)

  def list_services(self):
      request = lb.web.admin_pb2.Request()
      request.list.Clear()
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.list

  def list_handlers(self, id=None, get_local_config=False, get_global_config=False):
      request = lb.web.admin_pb2.Request()
      request.list_handlers.Clear()
      if id is not None:
        request.list_handlers.id = id
      if get_local_config:
        request.list_handlers.get_config = lb.web.admin_pb2.ListHandlersRequest.LOCAL
      elif get_global_config:
        request.list_handlers.get_config = lb.web.admin_pb2.ListHandlersRequest.GLOBAL
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.list_handlers

  def list_endpoints(self):
      request = lb.web.admin_pb2.Request()
      request.list_endpoints.Clear()
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)
      return response.list_endpoints

  def _init_scan_request(self, ws, scan):
      if isinstance(ws, dict):
          scan.workspace = ws['workspace']
          scan.host_workspace.extend(ws.get('host_workspaces', []))
          scan.load_services = ws.get('load_services',True)
          scan.load_realms = ws.get('load_realms',True)
          scan.load_cors = ws.get('load_cors',True)
      else:
          scan.workspace = ws

  def start_single_service(self, workspace):
      request = lb.web.admin_pb2.Request()
      request.stop.Clear()
      scan = request.start.request.add()
      self._init_scan_request(workspace, scan)
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)

  def start_exclusive_service_set(self, workspace_set):
      request = lb.web.admin_pb2.Request()
      request.stop.Clear()
      request.start.Clear()

      for ws in workspace_set:
        scan = request.start.request.add()
        self._init_scan_request(ws, scan)

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)

  def start_service(self, workspaces = []):
      request = lb.web.admin_pb2.Request()
      request.start.Clear()

      for ws in workspaces:
          scan = request.start.request.add()
          self._init_scan_request(ws, scan)

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
          raise RuntimeError(response.exception)

  def stop_service(self, workspaces = [], host_workspaces = []):
      request = lb.web.admin_pb2.Request()
      request.stop.Clear()
      request.stop.workspace.extend(workspaces)
      request.stop.host_workspace.extend(host_workspaces)

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
          raise RuntimeError(response.exception)


  def enable_service(self, prefix, endpoint = None, method = None):
      request = lb.web.admin_pb2.Request()
      request.enable.Clear()
      request.enable.service = prefix
      if (endpoint is not None):
          request.enable.endpoint = endpoint
      if (method is not None):
          request.enable.http_method = method

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)

  def disable_service(self, prefix, endpoint = None, status = None, method = None):
      request = lb.web.admin_pb2.Request()
      request.disable.Clear()
      request.disable.service = prefix
      if (endpoint is not None):
          request.disable.endpoint = endpoint
      if (status is not None):
          request.disable.status = int(status)
      if (method is not None):
          request.disable.http_method = method
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)
      if response.HasField("exception"):
          raise RuntimeError(response.exception)


  def get_service_specification(self, service_name):
      request = lb.web.admin_pb2.Request()
      request.spec.service = service_name

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
          raise RuntimeError("start service returned exception: %s" % response.exception)
      return response.spec.spec

  def set_log(self, category, enabled):
      request = lb.web.admin_pb2.Request()
      request.config.log.category = category
      request.config.log.enabled = enabled

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
          raise RuntimeError("start service returned exception: %s" % response.exception)

  def set_database_loglevel(self, log_level):
      request = lb.web.admin_pb2.Request()
      request.config.database_log_level = log_level;

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
        raise RuntimeError("start service returned exception: %s" % response.exception)

  def set_monitor_predicates(self, prednames,remove):
      request = lb.web.admin_pb2.Request()
      request.config.monitor = True
      if len(prednames)>0:
        request.config.predicate_name.extend(prednames)
      if remove:
        request.config.remove = True
      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
        raise RuntimeError("start service returned exception: %s" % response.exception)
      if response.update_config is not None:
        return response.update_config.predicate_name

  def set_workspace_monitor(self, pred_names, remove, ws_name=None):
      request = lb.web.admin_pb2.Request()
      request.config.monitor = True
      request.config.remove = remove
      if ws_name:
        request.config.ws_name = ws_name
      request.config.predicate_name.extend(pred_names)

      response = lb.web.admin_pb2.Response()
      self.client.call(request, response)

      if response.HasField("exception"):
        raise RuntimeError("workspace monitor returned exception: %s" % response.exception)
      if response.update_config is not None:
        return response.update_config.predicate_name
