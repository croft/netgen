import blox.connect.ConnectBlox_pb2 as cb
import blox.connect.io as io
import lb.web.service
import json

class BatchException(Exception):
    def __init__(self,message):
        self._message = message
    
    def __str__(self):
        return self._message
        
class BatchExecutor(object):
    def __init__(self,workspace):
        self.workspace = workspace
        self.prefix = None
        request = cb.Request()
        request.transaction.workspace = workspace
        cmd = request.transaction.command.add()
        cmd.query_predicate.predicate.global_name.qualified_name = "lb:web:workbooks:config:app_prefix"
        conn = io.Connection()
        conn.open()
            
        try:
            res = conn.call(request)
            prefixes= res.transaction.command[0].query_predicate.relation.column[0].string_column.values
            if len(prefixes) == 0:
                self.url = "/workbooks-batch"
            else:
                self.url = "/%s/workbooks-batch"%prefixes[0]
                
        except Exception,e:
            raise BatchException("Could not query app_prefix. Is workbook framework installed?")
        
    def run(self,id):
        

        client = lb.web.service.Client("localhost", 8080, self.url)
        message = client.dynamic_request()
        message.template_id = id
        message.execute = True
        res = client.dynamic_call(message)
        return res
