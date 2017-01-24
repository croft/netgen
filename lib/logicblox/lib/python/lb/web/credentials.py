import lb.web.service
import lb.web.credentials_pb2
import re

class CredentialError(Exception):

  def __init__(self, error_message, error_code): 
      self._error_message = error_message
      self._error_code = error_code
      
  def error_code(self):
      return self._error_code

  def __str__(self):
      return str(self._error_message) + " (code: " + self._error_code + ")"

class Client(object):

  def __init__(self, host = "localhost", port = "55183", path = "/admin/credentials"):
      self.client = lb.web.service.Client(host, port, path)

  def _check_error(self, response):
      if response.HasField("error") and response.HasField("error_code"):
          raise CredentialError(response.error, response.error_code)

  def get_by_username(self, username):
      request = lb.web.credentials_pb2.CredentialRequest()
      set = request.get.add()
      set.user_name = username
      return self.__get(request)

  def get_by_email(self, email):
      request = lb.web.credentials_pb2.CredentialRequest()
      set = request.get.add()
      set.email = email
      return self.__get(request)

  def get_by_token(self, token):
      request = lb.web.credentials_pb2.CredentialRequest()
      set = request.get.add()
      set.change_token = token
      return self.__get(request)

  def get_by_change_token(self, token):
      request = lb.web.credentials_pb2.CredentialRequest()
      set = request.get.add()
      set.change_token = token
      return self.__get(request)

  def __get(self, request):
      response = lb.web.credentials_pb2.CredentialResponse()
      self.client.call(request, response)
      self._check_error(response)
      return response.get[0]
  
  def set_password(self, username, password, create = False):
      request = lb.web.credentials_pb2.CredentialRequest()
      response = lb.web.credentials_pb2.CredentialResponse()

      set = request.set.add()
      set.user_name = username
      set.password_clear = password
      set.create = create

      self.client.call(request, response)
      self._check_error(response)

  def set_public_key(self, username, filename, create = False):
      request = lb.web.credentials_pb2.CredentialRequest()
      response = lb.web.credentials_pb2.CredentialResponse()

      key = ''
      state = 0
      pemfile = open(filename, 'r')
      for line in pemfile.readlines():
        if re.match("^----[-\ ]BEGIN PUBLIC KEY", line) and state == 0:
          state = 1
          continue
        elif re.match("^----[-\ ]END PUBLIC KEY", line) and state == 1:
          state = 2

        if state == 1:
          key = key + line.strip()

      if state != 2:
        raise RuntimeError("incorrect file format")

      set = request.set.add()
      set.user_name = username
      set.public_key = key
      set.create = create
      self.client.call(request, response)
      self._check_error(response)

  def set_active(self, username, active, create = False):
      request = lb.web.credentials_pb2.CredentialRequest()
      response = lb.web.credentials_pb2.CredentialResponse()

      set = request.set.add()
      set.user_name = username
      set.active = active
      set.create = create

      self.client.call(request, response)
      self._check_error(response)

  def list_users(self):
      request = lb.web.credentials_pb2.CredentialRequest()
      response = lb.web.credentials_pb2.CredentialResponse()

      request.list.Clear()
      self.client.call(request, response)
      self._check_error(response)

      return response.list.user
