require_relative '../lib/neatjson'
require_relative './tests'

pass  = 0
count = 0
$perftesting = %w[-p --perfest].include?(ARGV.first)
$large = JSON.parse(IO.read(File.expand_path('../large.json',__FILE__))) if $perftesting
start = Time.now
TESTS.each do |value_tests|
	val, tests = value_tests[:value], value_tests[:tests]
	tests.each do |test|
		cmd = "JSON.neat_generate(#{val.inspect},#{test[:opts].inspect})"
		begin
			json = test[:opts] ? JSON.neat_generate(val,test[:opts].dup) : JSON.neat_generate(val)
			raise "EXPECTED:\n#{test[:json]}\nACTUAL:\n#{json}" unless test[:json]===json
			pass += 1
		rescue StandardError => e
			puts "Failure running #{cmd}", e, ""
		end
		count += 1
		if $perftesting
			JSON.neat_generate($large,test[:opts]) rescue puts "Error serializing $large with #{test[:opts].inspect}"
		end
	end
end
elapsed = Time.now-start
elapsed = 0.0001 if elapsed==0
puts "%d/%d test#{:s if count!=1} passed in %.2fms (%d tests per second)" % [pass, count, elapsed*1000, count/elapsed]
