/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

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

