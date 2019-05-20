(function(exports){
exports.neatJSON = neatJSON;

function neatJSON(value,opts){
	opts = opts || {}
	if (!('wrap'          in opts)) opts.wrap = 80;
	if (opts.wrap==true) opts.wrap = -1;
	if (!('indent'        in opts)) opts.indent = '  ';
	if (!('arrayPadding'  in opts)) opts.arrayPadding  = ('padding' in opts) ? opts.padding : 0;
	if (!('objectPadding' in opts)) opts.objectPadding = ('padding' in opts) ? opts.padding : 0;
	if (!('beforeComma'   in opts)) opts.beforeComma   = ('aroundComma' in opts) ? opts.aroundComma : 0;
	if (!('afterComma'    in opts)) opts.afterComma    = ('aroundComma' in opts) ? opts.aroundComma : 0;
	if (!('beforeColon'   in opts)) opts.beforeColon   = ('aroundColon' in opts) ? opts.aroundColon : 0;
	if (!('afterColon'    in opts)) opts.afterColon    = ('aroundColon' in opts) ? opts.aroundColon : 0;
	if (!('beforeColon1'  in opts)) opts.beforeColon1  = ('aroundColon1' in opts) ? opts.aroundColon1 : ('beforeColon' in opts) ? opts.beforeColon : 0;
	if (!('afterColon1'   in opts)) opts.afterColon1   = ('aroundColon1' in opts) ? opts.aroundColon1 : ('afterColon'  in opts) ? opts.afterColon  : 0;
	if (!('beforeColonN'  in opts)) opts.beforeColonN  = ('aroundColonN' in opts) ? opts.aroundColonN : ('beforeColon' in opts) ? opts.beforeColon : 0;
	if (!('afterColonN'   in opts)) opts.afterColonN   = ('aroundColonN' in opts) ? opts.aroundColonN : ('afterColon'  in opts) ? opts.afterColon  : 0;

	var apad   = repeat(' ',opts.arrayPadding),
	    opad   = repeat(' ',opts.objectPadding),
	    comma  = repeat(' ',opts.beforeComma)+','+repeat(' ',opts.afterComma),
	    colon1 = repeat(' ',opts.beforeColon1)+':'+repeat(' ',opts.afterColon1),
	    colonN = repeat(' ',opts.beforeColonN)+':'+repeat(' ',opts.afterColonN);

	var build = memoize();
	return build(value,'');

	function memoize(){
		var memo = new Map;
		return function(o,indent){
			var byIndent=memo.get(o);
			if (!byIndent) memo.set(o,byIndent={});
			if (!byIndent[indent]) byIndent[indent] = rawBuild(o,indent);
			return byIndent[indent];
		}
	}

	function rawBuild(o,indent){
		if (o===null || o===undefined) return indent+'null';
		else{
			if (typeof o==='number'){
				var isFloat = (o === +o && o !== (o|0));
				return indent + ((isFloat && ('decimals' in opts)) ? o.toFixed(opts.decimals) : (o+''));
			}else if (o instanceof Array){
				if (!o.length) return indent+"[]";
				var pieces  = o.map(function(v){ return build(v,'') });
				var oneLine = indent+'['+apad+pieces.join(comma)+apad+']';
				if (opts.wrap===false || oneLine.length<=opts.wrap) return oneLine;
				if (opts.short){
					var indent2 = indent+' '+apad;
					pieces = o.map(function(v){ return build(v,indent2) });
					pieces[0] = pieces[0].replace(indent2,indent+'['+apad);
					pieces[pieces.length-1] = pieces[pieces.length-1]+apad+']';
					return pieces.join(',\n');
				}else{
					var indent2 = indent+opts.indent;
					return indent+'[\n'+o.map(function(v){ return build(v,indent2) }).join(',\n')+'\n'+(opts.indentLast?indent2:indent)+']';
				}
			}else if (o instanceof Object){
				var sortedKV=[],i=0;
				var sort = opts.sort || opts.sorted;
				for (var k in o){
					var kv = sortedKV[i++] = [k,o[k]];
					if (sort===true) kv[2] = k;
					else if (typeof sort==='function') kv[2]=sort(k,o[k],o);
				}
				if (!sortedKV.length) return indent+'{}';
				if (sort) sortedKV = sortedKV.sort(function(a,b){ a=a[2]; b=b[2]; return a<b?-1:a>b?1:0 });
				var keyvals=sortedKV.map(function(kv){ return [JSON.stringify(kv[0]), build(kv[1],'')] });
				if (opts.sorted) keyvals = keyvals.sort(function(kv1,kv2){ kv1=kv1[0]; kv2=kv2[0]; return kv1<kv2?-1:kv1>kv2?1:0 });
				keyvals = keyvals.map(function(kv){ return kv.join(colon1) }).join(comma);
				var oneLine = indent+"{"+opad+keyvals+opad+"}";
				if (opts.wrap===false || oneLine.length<opts.wrap) return oneLine;
				if (opts.short){
					keyvals = sortedKV.map(function(kv){ return [indent+' '+opad+JSON.stringify(kv[0]), kv[1]] });
					keyvals[0][0] = keyvals[0][0].replace(indent+' ',indent+'{');
					if (opts.aligned){
						var longest = 0;
						for (var i=keyvals.length;i--;) if (keyvals[i][0].length>longest) longest = keyvals[i][0].length;
						var padding = repeat(' ',longest);
						for (var i=keyvals.length;i--;) keyvals[i][0] = padRight(padding,keyvals[i][0]);
					}
					for (var i=keyvals.length;i--;){
						var k=keyvals[i][0], v=keyvals[i][1];
						var indent2 = repeat(' ',(k+colonN).length);
						var oneLine = k+colonN+build(v,'');
						keyvals[i] = (opts.wrap===false || oneLine.length<=opts.wrap || !v || typeof v!="object") ? oneLine : (k+colonN+build(v,indent2).replace(/^\s+/,''));
					}
					return keyvals.join(',\n') + opad + '}';
				}else{
					var keyvals=[],i=0;
					// TODO: share this code with sortedKV above
					for (var k in o){
						var kv = keyvals[i++] = [indent+opts.indent+JSON.stringify(k),o[k]];
						if (sort===true) kv[2] = k;
						else if (typeof sort==='function') kv[2]=sort(k,o[k],o);
					}
					if (sort) keyvals = keyvals.sort(function(a,b){ a=a[2]; b=b[2]; return a<b?-1:a>b?1:0 });
					if (opts.aligned){
						var longest = 0;
						for (var i=keyvals.length;i--;) if (keyvals[i][0].length>longest) longest = keyvals[i][0].length;
						var padding = repeat(' ',longest);
						for (var i=keyvals.length;i--;) keyvals[i][0] = padRight(padding,keyvals[i][0]);
					}
					var indent2 = indent+opts.indent;
					for (var i=keyvals.length;i--;){
						var k=keyvals[i][0], v=keyvals[i][1];
						var oneLine = k+colonN+build(v,'');
						keyvals[i] = (opts.wrap===false || oneLine.length<=opts.wrap || !v || typeof v!="object") ? oneLine : (k+colonN+build(v,indent2).replace(/^\s+/,''));
					}
					return indent+'{\n'+keyvals.join(',\n')+'\n'+(opts.indentLast?indent2:indent)+'}'
				}
			}else{
				return indent+JSON.stringify(o);
			}
		}
	}

	function repeat(str,times){ // http://stackoverflow.com/a/17800645/405017
		var result = '';
		while(true){
			if (times & 1) result += str;
			times >>= 1;
			if (times) str += str;
			else break;
		}
		return result;
	}

	function padRight(pad, str){
		return (str + pad).substring(0, pad.length);
	}
}
neatJSON.version = "0.8.3";

})(typeof exports === 'undefined' ? this : exports);
