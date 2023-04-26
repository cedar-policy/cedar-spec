package com.CedarDefinitionalImplementation.log;
import java.util.Optional;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ObjectNode;
import java.util.HashMap;



public class Logger {

	/* Singleton Infrastructure */
	private static Logger globalSingleton;

	public static Logger get() { 
		if (globalSingleton == null)
			globalSingleton = new Logger();
		return globalSingleton;
	}


	private HashMap<LogTag, Long> durations;

	private Logger() { 
		durations = new HashMap<>();
	}


	public <X> void set(LogTag tag, Timer<X> t) { 
		durations.put(tag, t.getDuration());
	}

	public long get(LogTag tag) { 
		if (durations.containsKey(tag)) 
			return durations.get(tag);
		else
			return 0;
	}
	


}

