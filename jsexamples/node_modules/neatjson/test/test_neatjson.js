var neatJSON = require('../javascript/neatjson.js').neatJSON;
var startTime = new Date;
var count=0, pass=0;
require('./tests.js').tests.forEach(function(valTest){
	var value = valTest.value;
	valTest.tests.forEach(function(test){
		var cmdOpts = test.opts ? JSON.parse(JSON.stringify(test.opts)) : '';
		if (test.opts && typeof test.opts.sort==='function') cmdOpts.sort = test.opts.sort+'';
		var cmd = "neatJSON("+JSON.stringify(value)+(test.opts?","+JSON.stringify(cmdOpts):'')+")";
		try{
			if (test.opts){
				var opts = {};
				for (var k in test.opts) opts[k] = test.opts[k];
				var json = neatJSON(value,opts);
			}else{
				var json = neatJSON(value);
			}
			var success = (test.json.constructor==RegExp) ? test.json.test(json) : json==test.json;
			if (success) pass+=1;
			else{
				console.log(cmd);
				console.log('EXPECTED');
				console.log(test.json);
				console.log('ACTUAL');
				console.log(json,"\n");
			}
		} catch(e) {
			console.log("Error running "+cmd);
			console.log(e.stack);
			console.log("")
		}
		count+=1;
	});
});
var elapsed = (new Date)-startTime;
console.log(pass+"/"+count+" test"+(count==1 ? '' : 's')+" passed in "+elapsed.toFixed(2)+"ms ("+(count/elapsed*1000).toFixed(0)+" tests per second)");

