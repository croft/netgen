import lb.web.admin
import lb.web.batch
import lb.web.credentials

from cli import lb_exception
from cli import util

from web import util as webutil

import blox.connect.ConnectBlox_pb2 as cb
import blox.connect.io as io
import lb.web.service
import json

from urlparse import urlparse

PRIVATE = 55183

def add_params(url, map):
    import urllib
    params = dict((k,v) for k,v in map.iteritems() if v is not None)
    if params:
        return url + '?' + urllib.urlencode(params)
    else:
        return url

class WorkbookException(Exception):
    pass

class Workbook(object):

    def __init__(self, json):
        self.json = json

    def id(self):
        return self.json.get('id', None)

    def name(self):
        return self.json.get('name', None)

class WorkbookTemplate(object):

    def __init__(self, json):
        self.json = json

    def id(self):
        return self.json.get('id', None)

    def name(self):
        return self.json.get('name', None)

class WorkbookManager(object):
    """ Python wrapper for workbook services
    """
    def __init__(self,master):
        """
        Args:
           master: the name of the master workspace
        """
        self.prefix = self.get_url_prefix(master)

    def get_url_prefix(self,workspace):
        """
        Use connectblox to query the app_prefix which defines URL for
        workbook services
        """

        request = cb.Request()
        request.transaction.workspace = workspace
        request.transaction.readonly = True
        cmd = request.transaction.command.add()
        cmd.query_predicate.predicate.global_name.qualified_name = "lb:web:workbooks:config:app_prefix"
        conn = io.Connection()
        conn.open()

        try:
            res = conn.call(request)
            if res.HasField('exception'):
                 raise WorkbookException(res.exception.message)
            prefixes= res.transaction.command[0].query_predicate.relation.column[0].string_column.values
            if len(prefixes) == 0:
                raise WorkbookException("No workbook service in %s\n:"%(workspace))
            else:
                url = "/%s/"%prefixes[0]
        except WorkbookException, e:
            raise e
        except Exception,e:
            raise WorkbookException("Could not locate workbook framework in %s:\n %s"%(workspace,e))
        return url[1:]

    def commit(self,workbook_id,json_string):
        """
        Args:
           json_string: the commit request message, as a json string
        """
        return self.commit_or_refresh(workbook_id,json_string,True)

    def refresh(self,workbook_id,json_string):
        """
        Args:
           json_string: the commit request message, as a json string
        """
        return self.commit_or_refresh(workbook_id,json_string,False)

    def commit_or_refresh(self,workbook_id,json_string,commit):

        call_name = "commit" if commit else "refresh"
        message = json.loads(json_string)
        message['workbook_id'] = workbook_id
        client = lb.web.service.Client("localhost", PRIVATE, "%sworkbooks/%s"%(self.prefix,call_name))
        try:
            return client.call_json(json.dumps(message))
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            print he
            raise WorkbookException("Commit failed: \n %s"%he.content())
        except Exception as e:
            raise WorkbookException("Commit failed: \n %s"%e)

    def create(self,spec):
        """
        Args:
            spec: the Workbook message as a json string
        Returns:
            The Workbook message as returned by the service
        """
        try:
            client = lb.web.service.Client("localhost", PRIVATE, "%sworkbooks"%(self.prefix))
            response = json.loads(client.call_json(spec))
            return Workbook(response)
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            print he
            raise WorkbookException("Creation failed: \n %s"%he.content())
        except Exception as e:
            raise WorkbookException("Creation failed: \n %s"%e)

    def delete(self, workbook_ids):
        try:
            url_params = '&'.join(["workbook-id=%s"%(id) for id in workbook_ids])
            client = lb.web.service.Client("localhost", PRIVATE, "%sworkbooks?%s"%(self.prefix, url_params))
            extra_headers = {'Accept': 'application/json'}
            response = client.send_call(body=None,method="DELETE",extra_headers=extra_headers)
            return response
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Deletion failed: \n %s"%he.content())
        except Exception as e:
            raise WorkbookException("Deletion failed: \n %s"%e)

    def delete_all(self):
        try:
            client = lb.web.service.Client("localhost", PRIVATE, "%sworkbooks?all=true"%self.prefix)
            extra_headers = {'Accept': 'application/json'}
            response = client.send_call(body=None,method="DELETE",extra_headers=extra_headers)
            return response
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Deletion failed: \n %s"%he.content())
        except Exception as e:
            raise WorkbookException("Deletion failed: \n %s"%e)

    def list(self, user_id=None, workbook_name=None, workbook_id=None, include_deleted=False, output='abbrev',template_name=None):
        '''List workbooks matching conditions.
        @param user_id    Only list workbooks for this user.
        @return           List of Workbook objects .'''

        id_only = None
        verbose = None
        active_only = None
        if output == 'id_only':
            id_only = True
        if output == 'verbose':
            verbose = True
        if include_deleted:
            active_only = False

        url = "%sworkbooks" % self.prefix
        url = add_params(url, {'user_id': user_id,
                               'workbook-id': workbook_id,
                               'workbook_name': workbook_name,
                               'template_name': template_name,
                               'active_only': active_only,
                               'id_only': id_only,
                               'verbose': verbose })
        client = lb.web.service.Client("localhost", PRIVATE, url)
        try:
            workbooks = json.loads(client.get_json())
            if id_only:
                return [ Workbook(json.loads('{ "id": "%s"}' % id)) for id in workbooks.get('id',[])]
            else:
                return [Workbook(wb) for wb in workbooks.get('workbooks',[])]
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to list workbooks: \n %s" % he)
        except Exception as e:
            raise WorkbookException("Failed to list workbooks: \n %s" % e)

    def create_template(self, spec_string):
        '''Install template in the workspace.
        @return WorkbookTemplate object.'''

        client = lb.web.service.Client("localhost", PRIVATE, "%sworkbook-templates"%(self.prefix))
        try:
            response = json.loads(client.call_json(spec_string))
            return WorkbookTemplate(response)
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to create template: \n %s" % he.content())
        except Exception as e:
            raise WorkbookException("Failed to create template: \n %s" % e)


    def list_templates(self, template_name=None, template_id=None):
        '''List workbook templates matching conditions.
        @param name   Template name.
        @param id     Template identifier.
        @return       List of WorkbookTemplate objects .'''

        url = "%sworkbook-templates" % self.prefix
        url = add_params(url, {'template-id': template_id, 'template-name': template_name})
        client = lb.web.service.Client("localhost", PRIVATE, url)
        try:
            templates = json.loads(client.get_json())
            return [WorkbookTemplate(tp) for tp in templates.get('templates',[])]
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to list templates: \n %s"%he.content())
        except Exception as e:
            raise WorkbookException("Failed to list templates: \n %s"%e)

    def delete_template(self, template_id):
        client = lb.web.service.Client("localhost", PRIVATE, "%sworkbook-templates?template-id=%s"%(self.prefix,template_id))
        extra_headers = {'Accept': 'application/json'}
        try:
            response = client.send_call(body=None,method="DELETE",extra_headers=extra_headers)
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to delete template %s: \n %s"%(template_id,he.content()))
        except Exception as e:
            raise WorkbookException("Failed to delete template %s: \n %s"%(template_id,e))

    def instantiate(self,json_string):
        client = lb.web.service.Client("localhost", PRIVATE, "%sworkbook-template-instantiation"%(self.prefix))
        try:
            response = json.loads(client.call_json(json_string))
            return Workbook(response['workbooks'][0])
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to instantiate : \n %s"%(he.content(),))
        except Exception as e:
            raise WorkbookException("Failed to instantiate : \n %s"%(e,))


    def users_request(self,user_list, workbook_id=None, workbook_name=None):
        if workbook_name is None:
            if workbook_id is None:
                raise WorkbookException("One and only one of id and name should be defined.")
            else:
                payload = json.dumps({"workbook_id":workbook_id,"user_id":user_list})
        else:
            if workbook_id is None:
                payload = json.dumps({"workbook_name":workbook_name,"user_id":user_list})
            else:
                raise WorkbookException("One and only one of id and name should be defined.")
        return payload

    def addusers(self, user_list, workbook_id=None, workbook_name=None):
        payload = self.users_request(user_list, workbook_id, workbook_name)
        client = lb.web.service.Client("localhost", PRIVATE, "%sworkbooks/addusers"%(self.prefix))
        try:
            return client.call_json(payload)
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to add users : \n %s"%(he.content(),))
        except Exception as e:
            raise WorkbookException("Failed to add users : \n %s"%(e,))


    def deleteusers(self, user_list, workbook_id=None, workbook_name=None):
        payload = self.users_request(user_list, workbook_id, workbook_name)
        client = lb.web.service.Client("localhost", PRIVATE, "%sworkbooks/deleteusers"%(self.prefix))
        try:
            return client.call_json(payload)
        except (lb.web.service.HttpClientError,lb.web.service.HttpServerError) as he:
            raise WorkbookException("Failed to delete users : \n %s"%(he.content(),))
        except Exception as e:
            raise WorkbookException("Failed to delete users %s: \n %s"%(e,))
