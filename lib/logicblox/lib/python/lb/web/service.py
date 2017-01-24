
from abc import ABCMeta, abstractmethod
import urlparse
import urllib2
import urllib
import lb.web.admin
import lb.web.protobuf_meta_pb2
import lb.web.protobuf_json
from google.protobuf import descriptor_pb2
from google.protobuf import descriptor_pool
from google.protobuf import message_factory

import cookielib
import json
import BaseHTTPServer
import time

from subprocess import Popen, PIPE, check_output

import StringIO
import gzip
import types
import csv
import re

class LBWebClientError(Exception):
    '''
    LB Web Client Error Exception class
    '''
    pass


class HttpError(Exception):
    '''A class that encapsulates information related to http request errors.'''

    def __init__(self, path, code, content=None, headers=None):
        '''Constructor

        @param path
		The url path for the failed request.
        @param code
		The http error code.
        @param content
		The error content.
        @param headers
		Headers set in the request.'''
        self._path = path
        self._code = code
        self._content = content
        self._headers = headers

    def path(self):
        '''Returns the request path for the failed request.'''
        return self._path

    def status_code(self):
        '''Returns the error status code.'''
        return self._code

    def headers(self):
        '''Returns the header for the request.'''
        return self._headers

    def content(self):
        '''Returns the error content.'''
        return self._content

    def status_short_message(self):
        '''Returns a short status message for the error.

        This is message is one from the BaseHTTPServer module.'''
        if self._code == 424:
            return "Failed Dependency"
        return BaseHTTPServer.BaseHTTPRequestHandler.responses[self.status_code()][0]

    def status_long_message(self):
        '''Returns a long, descriptive error message.

        This is message is one from the BaseHTTPServer module.'''
        if self._code == 424:
            return "The method could not be performed on the resource \
                    because the requested action depended on another \
                    action and that other action failed."
        return BaseHTTPServer.BaseHTTPRequestHandler.responses[self.status_code()][1]

    def __str__(self):
        return self.path() + ': ' + str(self.status_code()) + ' ' + self.status_short_message()


class HttpClientError(HttpError):
    '''An http error class for errors caused by the client.'''
    def __init__(self, path, code, content=None, headers=None):
        '''Constructor

        @param path
		The url path for the failed request.
        @param code
		The http error code.
        @param content
		The error content
        @param headers
		Headers set in the request.'''
        super(HttpClientError, self).__init__(path, code, content, headers)


class HttpServerError(HttpError):
    '''An http error class for errors caused by the server.'''
    def __init__(self, path, code, content=None, headers=None):
        '''Constructor

        @param path
		The url path for the failed request.
        @param code
		The http error code.
        @param content
		The error content.
        @param headers
		Headers set in the request.'''
        super(HttpServerError, self).__init__(path, code, content, headers)


def create_http_error(path, code, content=None, headers=None):
    '''Creates an HttpError object based on the error code.

    For error code >= 500 it creates a HttpServerError.
    For error codes between 400 and 499, creates an HttpClientError.

    @param path
		The url path for the failed request.
    @param code
		The http error code.
    @param content
		The error content.
    @param headers
		Headers set in the request.
    @return
		An HttpError object'''
    if code >= 400 and code <= 499:
        return HttpClientError(path, code, content, headers)
    if code >= 500 and code <= 599:
        return HttpServerError(path, code, content, headers)
    else:
        raise RuntimeError("not a http error code: '%s'" % (code))


class GenericClient(object):
  '''The base client class for all client services.'''

  def __init__(self, host, port, path, scheme = "http"):
      '''Constructor

      @param host
		The host for a service.
      @param port
		The port where the service is running.
      @param path
		The url path, after the host and port, for the running service.
      @param scheme
		The scheme to be used, for example http or https.'''

      self.scheme = scheme
      self.host = host
      self.port = port
      self.path = path
      self.jar = cookielib.CookieJar()

  @classmethod
  def from_url(cls, url):
    # it is unclear if disassembling the url is really such a great
    # idea, due to query parameters etc. It would perhaps have been
    # better if the client simply worked on a full url that it does
    # not know the structure of. However, this could break a lot of
    # client code, so we keep things as-is for now.
    o = urlparse.urlsplit(url)
    scheme = o.scheme
    host = o.hostname
    port = o.port
    path = o.path
    if o.query != "":
        path += "?%s" % (o.query)
    if o.fragment != "":
        path += "#%s" % (o.fragment)
    if port is None:
        if scheme == "https":
            port = 443
        elif scheme == "http":
            port  = 80
        else:
            raise RuntimeError("unsupported scheme: '%s'" % (scheme))
    return cls(host = host, port = port, path = path, scheme = scheme)

  def url(self):
      '''Returns the url string composed of the host, port, and path.

      @return
          The url for this service.'''
      return "%s://%s:%s%s" % (self.scheme, self.host, self.port, self.path)

  def http_exchange(self, method, headers = None, body = None, params = None, resource = ""):
      '''Performs an http request and returns the response.

      @param method
		The HTTP method, one of GET, HEAD, POST, or PUT.
      @param headers
		The headers to be set for this request.
      @param body
		The content of this request. The body wil be encoded as UTF-8.
      @param params
		Request parameters as a url string (param1=foo&param2=bar).
      @param resource
		The resource targeted by this request. This string will be
                appended to the url, such as http://localhost:8080/path/resource.
      @return
		A tuple of the response info and the response content.'''
      http_response = self.raw_http_exchange(method, headers, body, params, resource)
      return dict(http_response.info()), http_response.read()

  def raw_http_exchange(self, method, headers = None, body = None, params = None, resource = ""):
      '''Performs an http request and returns the response.

      @param method
    The HTTP method, one of GET, HEAD, POST, or PUT.
      @param headers
    The headers to be set for this request.
      @param body
    The content of this request. The body wil be encoded as UTF-8.
      @param params
    Request parameters as a url string (param1=foo&param2=bar).
      @param resource
    The resource targeted by this request. This string will be
                appended to the url, such as http://localhost:8080/path/resource.
      @return
    The http_response object returned by the urllib2 library.'''

      url = "%s%s" % (self.url(), resource)

      if params is not None and len(params) > 0:
        query_string = urllib.urlencode(params)
        url += '?' + query_string

      if method == 'GET' and body != None:
        raise RuntimeError('expected no body for GET')

      if method == 'HEAD' and body != None:
        raise RuntimeError('expected no body for HEAD')

      if method == 'POST' and body == None:
        raise RuntimeError('expected body for POST')

      if method == 'PUT' and body == None:
        raise RuntimeError('expected body for PUT')

      if headers is None:
        headers = {}

      http_req = urllib2.Request(url.encode('utf-8'), body, headers)
      http_req.get_method = lambda: method

      self.jar.add_cookie_header(http_req)
      try:
          http_response = urllib2.urlopen(http_req)
      except urllib2.HTTPError, e:
          raise create_http_error(self.path, e.code, e.read(), e.headers)
      except urllib2.URLError, e:
          if isinstance(e.reason, IOError):
            raise e.reason
          else:
            raise RuntimeError("service invocation failed %s: %s" % (self.path, e.args))
      self.jar.extract_cookies(http_response,http_req)
      return http_response

  def gzip_string(self, s):
      '''Compresses a string using gzip.

      @param s
		The string to be compressed.
      @return
		The compressed string.'''
      out = StringIO.StringIO()
      f = gzip.GzipFile(fileobj=out, mode='w')
      f.write(s)
      f.close()
      return out.getvalue()

  def gunzip_string(self, s):
      '''Uncompress an gzipped string.
      @param s
		A gzipped string.
      @return
		The uncompressed string.'''
      out = StringIO.StringIO(s)
      f = gzip.GzipFile(fileobj=out, mode='r')
      s2 = f.read()
      f.close()
      return s2


class ClientInterface(GenericClient):
    __metaclass__ = ABCMeta

    def __init__(self, host, port, path, scheme = "http"):
        '''Constructor

        @param host
		The host for a service.
        @param port
		The port where the service is running.
        @param path
		The url path, after the host and port, for the running service.'''
        super(ClientInterface, self).__init__(host, port, path, scheme = scheme)
        self.path = path
        self.classes = None

    def login(self, username, password, realm):
        """Login to the given realm.

        @param username
        @param password
        @param realm
        @return
		The JSON response of the service as an object."""
        req = self.dynamic_request()
        req.realm = realm
        req.username = username
        req.password = password
        resp = self.dynamic_call(req)
        return lb.web.protobuf_json.protobuf_to_dict(resp)

    def logout(self, realm):
        """Logout of the given realm.

        @param realm
        @return
		The JSON response of the service as an object."""
        response = self.call_json('{"logout":true,"realm":"%s"}' % (realm))
        return json.loads(response)

    @abstractmethod
    def dynamic_call(self, request, **kw):
        """Call service with a protobuf request, expecting a protobuf response.

        No response message object is needed, because the
        class is generated dynamically from the descriptor of the
        service protocols.

        @param request
        @param kw
		Other parameters to concrete instances of this interface."""
        pass

    @abstractmethod
    def call_json(self, request, **kw):
        """Call service with a JSON request, return a string, expected to be JSON.

        @param request
        @param kw
		Other parameters to concrete instances of this interface."""
        pass

    def get(self, response, extra_headers=None, gzip_resp = False):
      '''Performs a GET http request.

      @param response
		An empty protobuf message of the response type for this service.
      @param extra_headers
		Headers to be added to this request.
      @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
      @return
		The response of the call as a protobuf message'''
      response_string = self.send_call(body = None,
                                       extra_headers = extra_headers,
                                       gzip_req = False,
                                       gzip_resp = gzip_resp,
                                       method = 'GET')
      response.ParseFromString(response_string)
      return response

    def dynamic_get(self, extra_headers=None, gzip_resp = False):
      '''Performs a GET http request.

      @param extra_headers
		Headers to be added to this request.
      @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
      @return
		The response of the call as a protobuf message.'''
      if extra_headers is None:
        extra_headers = {}

      if 'Accept' not in extra_headers:
        extra_headers['Accept'] = 'application/octet-stream'
      else:
        extra_headers['Accept'] = extra_headers['Accept'] + "; application/octet-stream"

      return self.get(self.dynamic_response(), extra_headers, gzip_resp)

    def get_json(self, gzip_resp = False):
      '''Performs a GET http request.

      @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
      @return
		The response of the call as a protobuf message in JSON.'''
      headers = {"Accept":"application/json" }
      return self.send_call(body = None,
                            extra_headers = headers,
                            gzip_req = False,
                            gzip_resp = gzip_resp,
                            resp_content_type = "application/json",
                            method = 'GET')

    def send_call(self, body, extra_headers=None, gzip_req = False, gzip_resp = False, resp_content_type = None, method = 'POST'):
      '''Perform a call to the service.

      @param body
		The content for this request.
      @param extra_headers
		Headers to be added to the request.
      @param gzip_req
		 True if we should gzip the request.
      @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
      @param resp_content_type
		The expected return content type. Will throw an error if :
                                return content is different this.
      @param method
		The method of the http request.
      @return
		The unzipped response of the call as returned by http_exchange.'''
      headers = {}

      if body != None:
        headers["Content-Type"] = "application/octet-stream"
      if gzip_req:
        headers['Content-Encoding'] = 'gzip'
        body = self.gzip_string(body)
      if gzip_resp:
        headers['Accept-Encoding'] = 'gzip'

      # headers['Digest'] = 'SHA-512=' + base64.b64encode(hashlib.sha512(body).digest())
      if extra_headers is None:
        extra_headers = {}

      for extra in extra_headers:
        headers[extra] = extra_headers[extra]

      resp_headers, resp_body = self.http_exchange(method, headers, body)

      if resp_content_type != None:
        if 'content-type' not in resp_headers:
          raise RuntimeError("http response did not contain content-type header")
        ct = resp_headers['content-type'].split(';')[0]
        if ct != resp_content_type:
          raise RuntimeError("expected content-type '%s', but got '%s'" % (resp_content_type, ct))

      if gzip_resp and 'content-encoding' not in resp_headers:
        raise RuntimeError("expected to receive gzip encoded response, but did not")

      if gzip_resp and resp_headers['content-encoding'] == 'gzip':
        resp_body = self.gunzip_string(resp_body)

      return resp_body

    def dynamic_message(self, name):
        '''Returns an empty protobuf message.

        @param name
		The name of the message
        @return
		The protobuf message'''
        msg_class = self.classes[name]
        return msg_class()

    def dynamic_request(self):
        '''Returns an empty request protobuf message according to the service protocol.'''
        if self.classes is None:
            self.fetch_service_specification()
        return self.request_message_class()

    def dynamic_response(self):
        '''Returns an empty response protobuf message according to the service protocol.'''
        if self.classes is None:
            self.fetch_service_specification()
        return self.response_message_class()

    def fetch_service_specification(self):
        '''Queries the service for the message protocol specification.

        Does not return anything, but sets the request and response
        message classes for this service.'''
        path = self.path.split('?')[0]
        client = Client(self.host, self.port, path + '?meta=1', scheme = self.scheme)
        # share the cookie jar for authentication
        client.jar = self.jar

        request = lb.web.protobuf_meta_pb2.ProtoBufMetaRequest()
        response = lb.web.protobuf_meta_pb2.ProtoBufMetaResponse()
        request.protocol.Clear()

        response = client.call(request, response)
        spec = response.protocol

        self.request_message_name = spec.request_message_name
        self.response_message_name = spec.response_message_name

        request_descriptor = spec.request_descriptor
        response_descriptor = spec.response_descriptor

        request_fds = descriptor_pb2.FileDescriptorSet()
        request_fds.ParseFromString(request_descriptor)
        response_fds = descriptor_pb2.FileDescriptorSet()
        response_fds.ParseFromString(response_descriptor)
        pool = descriptor_pool.DescriptorPool()
        filenames = []
        for f in request_fds.file:
            filenames.append(f.name)
            pool.Add(f)
        for f in response_fds.file:
            filenames.append(f.name)
            pool.Add(f)
        factory = message_factory.MessageFactory()
        self.classes = {}
        for name in filenames:
            fd = pool.FindFileByName(name)
            for message_name,message in fd.message_types_by_name.items():
                full_name = message.full_name
                self.classes[full_name] =  factory.GetPrototype(pool.FindMessageTypeByName(full_name))

        self.request_message_class = self.classes[self.request_message_name]
        self.response_message_class = self.classes[self.response_message_name]


class Client(ClientInterface):

    def __init__(self, host, port, path, scheme = "http"):
        '''Constructor.

        @param host
		The host for a service.
        @param port
		The port where the service is running.
        @param path
		The url path, after the host and port, for the running service.'''
        super(Client, self).__init__(host, port, path, scheme = scheme)

    def call(self, request, response, extra_headers=None, gzip_req = False, gzip_resp = False, response_headers={}, params={}, async=False):
      '''Perform a call to the service.

      @param request
		A request protobuf message of the type specified by
                the service protocol.
      @param response
		An empty protobuf response message. Will be
                filled in with the call's response content.
      @param extra_headers
		Headers to be added to the request.
      @param gzip_req
		True if we should gzip the request.
      @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
      @param response_headers
        A Set to be populated with the headers from the response
      @param params
        Parameters to be included in the request query string.
      @param async
        Indicate if this request is asynchronous, so it should not try to parse the response.
      @return
		A response protobuf message with the result of this call'''
      if extra_headers is None:
        extra_headers = {}

      if 'Accept' not in extra_headers:
        extra_headers['Accept'] = 'application/octet-stream'
      else:
        extra_headers['Accept'] = extra_headers['Accept'] + "; application/octet-stream"
      request_string = request.SerializeToString()

      try:
        response_string = self.send_call(request_string, extra_headers, gzip_req, gzip_resp, response_headers=response_headers, params=params, async=async)
        if async:
            return response_string
      except HttpError, e:
        #parsing error content as a protobuf message and rethrowing. this is only necessary in the protobuf case
        if 'Content-Type' in e.headers() and e.headers()['Content-Type'] == "application/octet-stream" and e.content() is not None:
            content = e.content()
            # parse content as being of the response message type. If it either fails or has
            # unknown fields, try to parse as being of the generic error protocol.
            try:
                response.ParseFromString(content)
            except Exception,e2 :
                response = self._parse_as_error_message(content)

            if response._unknown_fields:
                response = self._parse_as_error_message(content)

            raise create_http_error(e.path(), e.status_code(), content=response, headers=e.headers())
        raise e

      response.ParseFromString(response_string)
      return response

    def _parse_as_error_message(self, content):
      ''' Parse this content as if it were protobuf according to the generic error response message.

      @param content the content to be parsed, as a string
      @return an object of the lb.web.error_report_pb2.Response type, if the content can be parsed
      as such a message.
      '''
      import lb.web.error_report_pb2
      response = lb.web.error_report_pb2.Response()
      response.ParseFromString(content)
      return response

    def dynamic_call(self, request, extra_headers=None, gzip_req=False, gzip_resp=False):
        '''Perform a call to the service.

        @param request
		A request protobuf message of the type specified by
                the service protocol.
        @param extra_headers
		Headers to be added to the request.
        @param gzip_req
		True if we should gzip the request.
        @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
        @return
		A response protobuf message with the result of this call.'''
        return self.call(request, self.dynamic_response(), extra_headers, gzip_req, gzip_resp)

    def call_json(self, request, gzip_req=False, gzip_resp=False):
        '''Make a call to the service with a JSON message as request.

        @param request
		A JSON string representing a protobuf message
                of the type specified by the service protocol.
        @param gzip_req
		True if we should gzip the request.
        @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
        @return
		The response of the call.'''
        headers = {
            "Content-Type": "application/json",
            "Accept": "application/json"}
        return self.send_call(request, extra_headers=headers,
                              gzip_req=gzip_req, gzip_resp=gzip_resp,
                              resp_content_type="application/json",
                              require_response=False)

    def get(self, response, extra_headers={}, gzip_resp=False):
        '''Performs a GET http request.

        @param response
		An empty protobuf message of the response type for this service.
        @param extra_headers
		Headers to be added to this request.
        @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
        @return
		The response of the call as a protobuf message.'''
        try:
            response_string = self.send_call(body=None,
                                             extra_headers=extra_headers,
                                             gzip_req=False,
                                             gzip_resp=gzip_resp,
                                             method='GET')
        except HttpError, e:
            #parsing error content as a protobuf message and rethrowing. this is only necessary in the protobuf case
            if 'Content-Type' in e.headers() and e.headers()['Content-Type'] == "application/octet-stream" and e.content() is not None:
                try:
                    response.ParseFromString(e.content())
                except Exception, e2:
                    import lb.web.error_report_pb2
                    response= lb.web.error_report_pb2.Response()
                    response.ParseFromString(e.content())

                raise create_http_error(e.path(), e.status_code(), content=response, headers=e.headers())
            raise e
        response.ParseFromString(response_string)
        return response

    def get_json(self, gzip_resp=False):
        '''Performs a GET http request.

        @param gzip_resp
		True if the response is gzipped. If so, we unzip the response.
        @return
		The response of the call as a protobuf message in JSON format.'''
        headers = {"Accept": "application/json"}
        return self.send_call(body=None,
                              extra_headers=headers,
                              gzip_req=False,
                              gzip_resp=gzip_resp,
                              resp_content_type="application/json",
                              method='GET')

    def send_call(self, body, extra_headers=None, gzip_req=False,
      gzip_resp=False, resp_content_type=None, method='POST',
      require_response=True, response_headers={}, params={}, async=False):
        '''Perform a call to the service.

        @param body
		The content for this request.
        @param extra_headers
		Headers to be added to the request.
        @param gzip_req
		True if we should gzip the request.
        @param gzip_resp
		True if the response is gzipped. If so, we unzip the response
        @param resp_content_type
		The expected return content type. Only type and subtype are considered, parameters are ignored.
    Will throw an error if return content is different than this.
        @param method
		The method of the http request.
        @param require_response
    Whether the call must contain response header and body with the appropriate
    content-type. If false, the server can return no content header.
        @param response_headers
        A Set to be populated with the headers from the response
        @param params
        Parameters to be included in the request query string.
        @param async
        Indicate if this request is asynchronous, so it should not try to parse the response.
        @return
		The unzipped response of the call as returned by http_exchange.'''
        headers = {}

        if body is not None:
            headers["Content-Type"] = "application/octet-stream"
        if gzip_req:
            headers['Content-Encoding'] = 'gzip'
            body = self.gzip_string(body)
        if gzip_resp:
            headers['Accept-Encoding'] = 'gzip'

        # headers['Digest'] = 'SHA-512=' + base64.b64encode(hashlib.sha512(body).digest())

        if extra_headers is not None:
          for extra in extra_headers:
              headers[extra] = extra_headers[extra]

        resp_headers, resp_body = self.http_exchange(method, headers, body, params)
        response_headers.update(resp_headers)
        if async:
            return resp_body
        else:
            return self.parse_call_response(resp_headers, resp_body, resp_content_type, gzip_resp, require_response)

    def parse_call_response(self, resp_headers, resp_body, resp_content_type = None, gzip_resp = False, require_response=True):
        '''Validates and unzip the response when applicable

        @param resp_headers
        The headers from the response to be parsed
        @param resp_body
        The body of the response to be parsed
        @param resp_content_type
        The expected return content type. Only type and subtype are considered, parameters are ignored.
    Will throw an error if return content is different than this.

        @param gzip_resp
        True if the response is gzipped. If so, we unzip the response
        '''
        if resp_content_type is not None:
            if 'content-type' not in resp_headers:
                if require_response:
                  raise RuntimeError("http response did not contain content-type header")
            else:
              ct = resp_headers['content-type'].split(';')[0]
              if ct != resp_content_type:
                  raise RuntimeError("expected content-type '%s', but got '%s'" % (resp_content_type, ct))

        if gzip_resp and 'content-encoding' not in resp_headers:
            raise RuntimeError("expected to receive gzip encoded response, but did not")

        if gzip_resp and resp_headers['content-encoding'] == 'gzip':
            resp_body = self.gunzip_string(resp_body)

        return resp_body


class DelimClientInterface(object):
    '''An interface for a client for delimited file services.'''
    __metaclass__ = ABCMeta

    @abstractmethod
    def get(self, gzip=False, txn=False, params=None, delimiter='|'):
        '''Performs a GET request on a delimited file service.

        @param gzip
		True if the response should be compressed.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.'''
        pass

    @abstractmethod
    def put(self, delim, gzip=False, extra_headers={}, txn=None, return_errors=True, abort_on_error=None, params=None):
        """Performs an HTTP PUT of the given delimited file.

        @param delim
		The content of a delimited file as string or a DelimitedFile instance.
        @param gzip
		True if the response should be compressed.
        @param extra_headers
		Headers to be added to the request.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @param return_errors
		If return_errors is True, returns the body of the response from the server.
        @param abort_on_error
		If True, aborts the transaction on error.
        @return
		The body of the error response message if return_errors is True.
        """
        pass

    @abstractmethod
    def post(self, delim, gzip=False, extra_headers={}, txn=None, return_errors=True, abort_on_error=None, params=None):
        """Performs an HTTP POST of the given delimited file.

        @param delim
		The content of a delimited file as string or a DelimitedFile instance.
        @param gzip
		True if the response should be compressed.
        @param extra_headers
		Headers to be added to the request.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @param return_errors
		If return_errors is True, returns the body of the response from the server.
        @param abort_on_error
		If True, aborts the transaction on error.
        @return
		The body of the error response message if return_errors is True.
        """
        pass


class DelimClient(DelimClientInterface, GenericClient):

   # Warning: this implementation is not even remotely designed to be
   # efficient. The purpose of this class is mainly to assist in unit
   # testing.

    def __init__(self, host, port, path, scheme = "http"):
        '''Constructor.

        @param host
		The host for a service.
        @param port
		The port where the service is running.
        @param path
		The url path, after the host and port, for the running service.'''
        super(DelimClient, self).__init__(host, port, path, scheme = scheme)

    def dynamic_file(self):
        '''Returns an empty delimited file.'''
        return DelimitedFile()

    def get_raw(self, gzip=False, txn=None, params=None):
        '''Performs a GET request on a delimited file service.

        @param gzip
		True if the response should be compressed.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @return
		A tuple with the response headers and the response of the
                delimited file request as a string.'''
        getheaders = {}
        if gzip:
            getheaders = {"Accept-Encoding": "gzip"}

        if params is None:
          params = {}
        if txn is not None:
            params['txn'] = txn.txnid
            txn.count += 1

        headers, body = self.http_exchange('GET', headers=getheaders, params=params)
        if gzip:
            body = self.gunzip_string(body)
        return headers, body

    def get(self, gzip=False, txn=None, params=None, delimiter='|'):
        '''Performs a GET request on a delimited file service.

        @param gzip
		True if the response should be compressed.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @return
		A delimited file.'''
        headers, body = self.get_raw(gzip, txn=txn, params=params)

        # if this is a GET on an async transaction, return the location of the new part
        if txn is not None and txn.async:
          part_id = headers['location'].rpartition('/')[2]
          txn.part_ids.add(part_id)
          return part_id

        delim = DelimitedFile(delimiter)
        delim.add_string(body)
        return delim

    def put(self, delim, gzip=False, extra_headers={}, txn=None, return_errors=True, abort_on_error=None, params=None, raw=False, response_headers=None):
        """Performs an HTTP PUT of the given delimited file.

        @param delim
		The content of a delimited file as string or a DelimitedFile instance.
        @param gzip
		True if the response should be compressed.
        @param extra_headers
		Headers to be added to the request.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @param return_errors
		If return_errors is True, returns the body of the response from the server.
        @param abort_on_error
		If True, aborts the transaction on error.
        @param raw
    Treat the delim param as a raw string to be sent in the wire, instead of attempting to quote and escape.
        @param response_headers
    A dict that will be updated with the headers returned by the response. This is necessary because this method returns only
    the response body and, to avoid breaking backwards compatibility, we use mutable parameters.
        @return
		The body of the error response message if return_errors is True.
        """
        return self.upload_helper('PUT', delim, gzip, extra_headers, txn, return_errors, abort_on_error, params, raw, response_headers)

    def post(self, delim, gzip=False, extra_headers={}, txn=None, return_errors=True, abort_on_error=None, params=None, raw=False, response_headers=None):
        """Performs an HTTP POST of the given delimited file.

        @param delim
		The content of a delimited file as string or a DelimitedFile instance.
        @param gzip
		True if the response should be compressed
        @param extra_headers
		Headers to be added to the request.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @param return_errors
		If return_errors is True, returns the body of the response from the server.
        @param abort_on_error
		If True, aborts the transaction on error.
        @param raw
    Treat the delim param as a raw string to be sent in the wire, instead of attempting to quote and escape.
        @param response_headers
    A dict that will be updated with the headers returned by the response. This is necessary because this method returns only
    the response body and, to avoid breaking backwards compatibility, we use mutable parameters.
        @return
		The body of the error response message if return_errors is True.
        """
        return self.upload_helper('POST', delim, gzip, extra_headers, txn, return_errors, abort_on_error, params, raw, response_headers)

    def upload_helper(self, method, delim, gzip, extra_headers, txn, return_errors=True, abort_on_error=None, params=None, raw=False, response_headers=None):
        '''Performs an upload of a delimited file to the service.

        @param method
		The HTTP request method.
        @param delim
		The content of a delimited file as string or a DelimitedFile instance.
        @param gzip
		True if the response should be compressed.
        @param extra_headers
		Headers to be added to the request.
        @param txn
		An existing transaction for this request. If False or None,
                a new transaction is created.
        @param return_errors
		If return_errors is True, returns the body of the response from the server. If it is None or "on_error", then
    the error file will only be returned if there are errors. Otherwise, do not return errors.
        @param abort_on_error
		If True, aborts the transaction on error.
        @param params
    Additional parameters for request as a dictionary.
        @param raw
    Treat the delim param as a raw string to be sent in the wire, instead of attempting to quote and escape.
        @param response_headers
    A dict that will be updated with the headers returned by the response. This is necessary because this method returns only
    the response body and, to avoid breaking backwards compatibility, we use mutable parameters.
        @return
    If this is part of an async transaction, return the id of the newly created part on the transaction.
		Otherwise return the contents of the response.
        '''
        if not raw and not isinstance(delim, DelimitedFile):
            delim = DelimitedFile.from_dynamic(delim)

        headers = {
            "Content-Type": "text/csv",
            "Accept": "text/csv"
        }
        for extra in extra_headers:
            headers[extra] = extra_headers[extra]

        body = delim if raw else delim.to_string()
        if gzip:
            body = self.gzip_string(body)
            headers['Content-Encoding'] = 'gzip'

        if not params:
          params = {}

        # if return_errors is present in params, do not override
        if 'return_errors' not in params:
            if return_errors is True:
              params['return_errors'] = '1'
            elif return_errors is None or return_errors == 'on_error':
              params['return_errors'] = 'on_error'
            else:
              params['return_errors'] = '0'

        if abort_on_error is True:
          params['abort_on_error'] = '1'
        if abort_on_error is False:
          params['abort_on_error'] = '0'

        if txn is not None:
          params['txn'] = txn.txnid
          txn.count += 1

        headers, body = self.http_exchange(method, headers, body, params)
        if isinstance(response_headers, dict):
          response_headers.update(headers)
        if txn is not None and txn.async:
          part_id = headers['location'].rpartition('/')[2]
          txn.part_ids.add(part_id)
          return part_id
        return body



class DynamicDelimClient(DelimClient):
    """A class which uses a dynamic TDX service but mimics a static TDX
    client by sending the same file_binding to each request.
    This is convenient for sharing tests.
    """
    def __init__(self, host, port, path, params, scheme = "http"):
        '''Constructor.

        @param host
		The host for a service.
        @param port
		The port where the service is running.
        @param path
		The url path, after the host and port, for the running service.
        @param params
                The extra parameters to send with each request'''

        super(DynamicDelimClient, self).__init__(host, port, path, scheme = scheme)
        self._params=params

    def get(self, gzip=False, txn=None, delimiter='|'):
        return super(DynamicDelimClient,self).get(gzip=gzip,txn=txn,params=self._params,delimiter=delimiter)

    def put(self, delim, gzip=False, extra_headers={}, txn=None, return_errors=True, abort_on_error=None):
        return super(DynamicDelimClient,self).put(delim, gzip=gzip, extra_headers=extra_headers, return_errors=return_errors, abort_on_error=abort_on_error, params=self._params)

    def post(self, delim, gzip=False, extra_headers={}, txn=None, return_errors=True, abort_on_error=None):
        return super(DynamicDelimClient,self).post(delim, gzip=gzip, extra_headers=extra_headers, return_errors=return_errors, abort_on_error=abort_on_error, params=self._params)


class DelimitedFile(object):
  """In-memory representation of a delimited-file.

  This implementation is not designed to scale to large
  delimited-files. It should be used mainly for writing unit tests.
  """

  def __init__(self, delimiter = '|'):
      '''Constructor

      @param delimiter
		The delimiter to use for the string representation
                of this delimited file'''
      self._cells = []
      self._format = {'delimiter' : delimiter,
                     'quoting' : csv.QUOTE_MINIMAL,
                     'escapechar' : '\\',
                     'doublequote' : False,
                     'lineterminator' : '\n',
                     'strict' : True}

  def _read_file(self, f):
      reader = csv.reader(f,  **self._format)
      return reader

  def _read_string(self, s):
      f = StringIO.StringIO(s)
      return self._read_file(f)

  def _write_file(self, f):
      writer = csv.writer(f, **self._format)
      for row in self.cells():
        writer.writerow(row)

  def add_lines(self, lines):
      """Add a sequences of string lines to the delimited file.

      The lines are not stripped from whitespace.
      """
      for line in lines:
        self._cells.append(tuple(self._read_string(line).next()))

  def add_string(self, s):
      """Add the given string to the delimited file.

      The lines in the string are stripped from whitespace to make it
      easy to use multi-line string literals in Python source code.
      """
      lines = filter(None, [line.strip() for line in s.splitlines()])
      self.add_lines(lines)

  def to_string(self):
      """Convert this delimitded file to a string, using the specified delimiter."""
      output = StringIO.StringIO()
      self._write_file(output)
      return output.getvalue()

  def _tuple_to_string(self, t):
      f = StringIO.StringIO()
      writer = csv.writer(f, **self._format)
      writer.writerow(t)
      return f.getvalue()

  def cells(self):
      """Returns a list of tuples representing the rows in this file.

      This list should not be modified.
      """
      return self._cells

  def lines(self):
      """Returns a list of rows, represented as a string using the delimiter of this file.

      Compared to returning a full string,
      this method can be useful when writing tests that need to ignore
      ordering of lines."""
      return [self._tuple_to_string(row) for row in self.cells()]

  def linecount(self):
      """Returns the number of lines in this file (including possible header)."""
      return len(self.cells())

  @classmethod
  def from_dynamic(cls, data):
      '''Build a DelimitedFile from data.

      @param data
		A list of lines or a string.'''
      if isinstance(data, types.ListType):
        return cls.from_lines(data)
      elif isinstance(data, basestring):
        return cls.from_string(data)
      else:
        raise RuntimeError('expected string or list as argument to from_dynamic')

  @classmethod
  def from_string(cls, s):
      '''Build a DelimitedFile from data.

      @param data
		A string.'''
      delim = cls()
      delim.add_string(s)
      return delim

  @classmethod
  def from_lines(cls, lines):
      '''Build a DelimitedFile from data.

      @param data
		A list of lines.'''
      delim = cls()
      delim.add_lines(lines)
      return delim

  @classmethod
  def from_file(cls, filename):
      '''Build a DelimitedFile from data found in a file.'''
      with open(filename, "r") as f:
        return cls.from_string(f.read())


class DelimTxnClient(DelimClient):
  '''A client to a delimited transaction service.'''

  def __init__(self, host, port, path, scheme = "http"):
      '''Constructor

      @param host
      @param port
      @param path'''
      super(DelimClient, self).__init__(host, port, path, scheme = scheme)
      self.count = 0

  def start(self, async=False):
      '''Start the transaction.

      @param async whether the transaction should use the asynchronous protocol.
      '''
      params = {} if not async else {'async': 'true'}
      resp_headers, resp_body = self.http_exchange(
        'POST',
        headers = {},
        body = '',
        params = params,
        resource = "/start")
      return DelimTxn(resp_headers['location'].rpartition('/')[2], async)

  def commit(self, txn):
      '''Commit the transaction.'''
      if (txn.async):
        headers = {'content-type': 'application/json'}
        body = '{ part_id: [' + ','.join(map(lambda id: "'%s'" % id, txn.part_ids)) + ']}'
      else:
        headers = {}
        body = ''
      resp_headers, resp_body = self.http_exchange(
        'POST',
        headers = headers,
        body = body,
        params = {'count' : txn.count},
        resource = "/%s/commit" % txn.txnid)
      return resp_body

  def abort(self, txn):
      '''Abort the transaction.'''
      resp_headers, resp_body = self.http_exchange(
        'POST',
        headers = {},
        body = '',
        params = {},
        resource = "/%s/abort" % txn.txnid)
      return resp_body

  def is_ongoing(self, txn):
      '''Check whether the async transaction is ongoing or if it finished.

      @param txn the DelimTxn object representing the transaction.
      @return True if the transaction is still ongoing, False otherwise.
      '''
      # poll returns 201 if it's ongoing, and 303 when it's done. However,
      # urlib2 performs the redirect on 303. So we know that the transaction
      # is ongoing if there was no redirect, i.e., the returned url remains poll
      resp = self.raw_http_exchange("GET", resource = "/%s/poll" % txn.txnid)
      return resp.geturl().endswith('/poll')


  def poll(self, txn, delay=5):
      '''Block until the transaction is over (not is_ongoing), checking every
      delay seconds.

      @param txn the DelimTxn object representing the transaction.
      @param delay number of seconds to wait before checking again whether the
      transaction is still ongoing.
      '''
      while(True):
        if not self.is_ongoing(txn):
          return
        time.sleep(delay)


  def get_list(self, media_type='text/plain'):
      '''GET list of transactions. Supports 'text/plain' and 'application/json'.

      @param txn the DelimTxn object representing the transaction.
      @param media_type the type of content to request.
      @return the body of the response.
      '''
      headers = {'Accept': media_type}
      return self._get_info(resource = "", headers = headers)

  def get_info(self, txn, media_type='text/plain'):
      '''GET transaction information. Supports 'text/plain' and 'application/json'.

      @param txn the DelimTxn object representing the transaction.
      @param media_type the type of content to request.
      @return the body of the response.
      '''
      headers = {'Accept': media_type}
      return self._get_info(resource = "/%s" % txn.txnid, headers = headers)

  def get_part_file(self, txn, part_id):
      return self.get_part_info(txn, part_id, 'text/csv')

  def get_part_info(self, txn, part_id, media_type='text/plain'):
      '''GET transaction part information.  Supports 'text/plain', 'application/json' and 'text/csv'.

      @param txn the DelimTxn object representing the transaction.
      @param part_id the id of the part from which info is to be taken.
      @param media_type the type of content to request.
      @return if media_type is text/csv, return a DelimitedFile object with the body of the response;
        otherwise return the body of the response.
      '''
      headers = {'Accept': media_type}
      body = self._get_info(resource = "/%s/%s" % (txn.txnid, part_id), headers = headers)
      if media_type == 'text/csv':
        delim = lb.web.service.DelimitedFile()
        delim.add_string(body)
        return delim
      return body

  def _get_info(self, resource, headers):
      return self.raw_http_exchange("GET", resource=resource, headers=headers).read()


class DelimTxn(object):
    '''A delimited file service transaction.'''

    def __init__(self, txnid, async=False):
        '''Constructor

        @param txnid
		The id of the transaction.'''
        self.txnid = txnid
        self.count = 0
        self.async = async
        self.part_ids = set()

class AsyncClient(object):
    __metaclass__ = ABCMeta

    def start(self, method="GET", data=None, gzip=False, txn=None, raw=False, extra_headers={}, params={}):
        '''Start the async transaction, by sending the first request.

        @param method
        The method of the request to be sent
        @param data
        The body
        @param extra_headers
        Additional headers to be sent in the request
        @return The id of this asynchronous transaction and the url to poll for the result
        '''

        resp_headers, resp_body = self._send_request(method, data=data, gzip=gzip, txn=txn, raw=raw,extra_headers=extra_headers, params=params)
        polling_location = resp_headers['location']
        parsed = urlparse.urlparse(polling_location)
        async_id = urlparse.parse_qs(parsed.query)['lb_async_id']
        return async_id, polling_location

    def poll(self, polling_location, delay=0.1):
        '''Polls a given url until it returns a 303 redirect with the response URL.

        @param polling_location
        The URL to be polled
        @param delay
        polling interval
        @return the URL for the final response, once ready.
        '''
        httpClient = Client.from_url(polling_location)

        # The from_url method creates a new instance, so we need to propagate the
        # cookies, otherwise authentication will fail
        httpClient.jar = self.jar
        http_response = httpClient.raw_http_exchange(method="GET")
        code = http_response.code

        while (code == 200):
            http_response = httpClient.raw_http_exchange(method="GET")
            code = http_response.code

        response = http_response.read()
        headers = dict(http_response.info())

        if (code <> 303):
            print "Error. Polling returned a status different than 200 or 303"
            raise create_http_error(polling_location, headers.status, content=response, headers=headers)
        return headers["location"]

    def get_response(self, location, delete=True):
        '''Invoke the final location URL, to get the response of the async processing.
        It will also uncompress the body content if the response is compressed.
        In the end, if delete param is True, it will also send a DELETE HTTP request
        to delete the response from the server cache. This is recommended to free up memory
        and disk resources.
        @param location
        The URL returned from polling.
        @param delete
        Whether we should ask the server to free up resources, by deleting the response from cache.
        '''
        client = Client.from_url(location)
        # The from_url method creates a new instance, so we need to propagate the
        # cookies, otherwise authentication will fail
        client.jar = self.jar

        headers, body = client.http_exchange(method="GET")
        if headers.get('content-encoding','') == 'gzip':
            body = self.gunzip_string(body)

        if delete:
            self.delete_response(location)
        return headers, body

    def delete_response(self, response_location):
        '''Send a DELETE HTTP request to delete the response from the server cache.
        This is recommended to free up memory and disk resources.

        @param response_location
        The final response URL
        '''
        parsed = urlparse.urlparse(response_location)
        if 'X-HTTP-Method-Override' not in urlparse.parse_qs(parsed.query):
            response_location += '&X-HTTP-Method-Override=GET'

        client = Client.from_url(response_location)
        # The from_url method creates a new instance, so we need to propagate the
        # cookies, otherwise authentication will fail
        client.jar = self.jar

        headers, response = client.http_exchange(method="DELETE")
        return headers, response

    def abort(self, polling_location):
        '''Aborts an ongoing async request.
        @param polling_location
        The polling URL.
        '''

        client = Client.from_url(polling_location)
        # The from_url method creates a new instance, so we need to propagate the
        # cookies, otherwise authentication will fail
        client.jar = self.jar

        headers, response = client.http_exchange(method="DELETE")
        return headers, response

    def handle_async_protocol(self, method, data="", gzip=False, params={}, extra_headers={}, delete=True):
        '''Utility method that handles all the lifecycle of an async GET request.
        It will start the request, poll, get the response, and parse the response.

        @param method:
        The HTTP method
        @param data:
        The request body.
        @param gzip:
        If request and response should be compressed.
        @param extra_headers
        Extra headers to be sent in the HTTP request.
        @param params:
        Extra parameters to be added to the HTTP query string

        @return:
        The final async response, parsed into an instance of DelimitedFile.
        '''

        async_id, polling_location = self.start(method, data=data, gzip=gzip, params=params, extra_headers=extra_headers)
        response_location = self.poll(polling_location)
        headers, resp_body = self.get_response(response_location, delete)
        return self._parse_response(resp_body)

    @abstractmethod
    def _send_request(self, method="GET", data=None, gzip=False, txn=None, raw=False, extra_headers={}, params={}):
        '''This abstract method is called by the start method, to send the actual async request.
        @param method:
        The HTTP method
        @param data:
        The body of the HTTP request. Note that for Protobuf this is dynamic_request object
        while for tdx it's an array with each line.
        @param gzip:
        If True, it will compress the POST/PUT data, and also send the accept-encoding:gzip header.
        @param txn:
        Used in TDX transactions.
        @param raw:
        For TDX clients, treat the delim param as a raw string to be sent in the wire,
        instead of attempting to quote and escape.
        @param extra_headers:
        Extra HTTP headers to be sent in the start request.
        @param params:
        Extra HTTP request parameters to be added to the query string.

        @return: headers, response
        A Dictionary including all HTTP headers, and the body, from the response of this invocation.
        '''
        pass

    @abstractmethod
    def _parse_response(self, resp_body):
        '''Abstract method called by 'handle' to parse the final response.
        @param resp_body:
        The body from the response to be parsed
        '''
        pass

class AsyncTdxClient(AsyncClient, DelimClient):
    ''' The implementation of AsyncClient for a TDX client.'''
    def __init__(self, host, port, path, scheme = "http"):
        '''Constructor

        @param host
        @param port
        @param path'''
        super(DelimClient, self).__init__(host, port, path, scheme = scheme)
        opener = urllib2.build_opener(NoRedirectHandler())
        urllib2.install_opener(opener)

    def _send_request(self, method="GET", data=None, gzip=False, txn=None, raw=False, extra_headers={}, params={}):
        '''Implements the abstract method _send_request. This method is called in the start
        method from the abstract super class, to submit the async request.
        '''
        resp_headers = {}
        resp_body = None
        if params is None:
            params = {}
        if extra_headers is None:
            extra_headers = {}
        if gzip:
            extra_headers.update({"Accept-Encoding": "gzip"})

        params.update({'lb_async':'true'})

        if (method == 'POST'):
            resp_body = self.post(delim=data, gzip=gzip, txn=txn, extra_headers=extra_headers, params=params, raw=raw, response_headers=resp_headers)
        elif (method == 'PUT'):
            resp_body = self.put(delim=data, gzip=gzip, txn=txn, extra_headers=extra_headers, params=params, raw=raw, response_headers=resp_headers)
        else:
            if txn is not None:
                params['txn'] = txn.txnid
                txn.count += 1
            resp_headers, body = self.http_exchange('GET', headers=extra_headers, params=params)


        return resp_headers, resp_body

    def _parse_response(self, body):
        '''Implementation of the abstract method _parse_response. This method is called
        in the handle method from the abstract super class.
        '''
        delim = DelimitedFile()
        delim.add_string(body)
        return delim

class AsyncProtobufClient(AsyncClient, Client):
    '''AsyncClient implementation for Protobuf services.
    '''
    def __init__(self, host, port, path, scheme = "http"):
        '''Constructor

        @param host
        @param port
        @param path'''
        super(Client, self).__init__(host, port, path, scheme = scheme)
        opener = urllib2.build_opener(NoRedirectHandler())
        urllib2.install_opener(opener)

    def _send_request(self, method="GET", data=None, gzip=False, txn=None, raw=False, extra_headers={}, params={}):
        '''Implements the abstract method send_request. This method is called in the start
        method from the abstract super class, to submit the async request.
        '''

        response_headers={}
        if params is None:
            params = {}
        params.update({'lb_async':'true'})

        resp_body = self.call(data, self.dynamic_response(), extra_headers, response_headers=response_headers,params=params, async=True)

        return response_headers, resp_body

    def get_protobuf_response(self, response_location):
        '''Utility method to get the response and parse the response into a
        dynamic_response.
        @param response_location:
        The URL of the Async final response

        @return: dynamic_response object parsed from the response.
        '''
        resp_headers, http_response = self.get_response(response_location)
        http_response = self.parse_call_response(resp_headers, http_response)
        return self._parse_response(http_response)

    def _parse_response(self, body):
        '''Implementation of the abstract method _parse_response. This method is called
        in the handle method from the abstract super class.
        '''
        protobuf_response = self.dynamic_response()
        protobuf_response.ParseFromString(body)
        return protobuf_response

class NoRedirectHandler(urllib2.HTTPRedirectHandler):
    '''This class is used because urllib2 by default follows redirects.
    We need to override the behaviour if we want to skip automatic redirections.
    '''

    def http_error_302(self, req, fp, code, msg, headers):
        infourl = urllib.addinfourl(fp, headers, req.get_full_url())
        infourl.status = code
        infourl.code = code
        return infourl
    http_error_300 = http_error_302
    http_error_301 = http_error_302
    http_error_303 = http_error_302
    http_error_307 = http_error_302
