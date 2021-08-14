"use strict";
var http = require('http');
const execSync = require('child_process').execSync;

function runShellCommand(arg) {
    console.log(arg);
    var r = execSync(`core.exe ${arg.replace(/(?:\")/g, "~")}`);
    var s = r.toString();
    var x = s.toString().replace(/(?:\r\n|\r|\n)/g, '').replace(/(?:\\")/g, '\"');
    return x.slice(1,  x.length - 1);
}

http.createServer(function(req, res) {
    res.setHeader('Content-Type', 'text/json'); 
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS, PUT, PATCH, DELETE'); // If needed
    res.setHeader('Access-Control-Allow-Headers', 'X-Requested-With,content-type'); // If needed
    res.setHeader('Access-Control-Allow-Credentials', true);
    res.writeHead(200);
    req.on('data',function(message){
        var m = message.toString().replace(/(?:\r\n|\r|\n)/g, '');        
        console.log("m", m);
        var r = runShellCommand(`${m}`);
        res.write(`${r}`);
    });
    req.on('end',function(){
        res.end();
    });
}).listen(8000);

