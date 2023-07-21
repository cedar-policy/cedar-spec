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

package com.CedarDefinitionalImplementation;

import com.CedarDefinitionalImplementation.log.Timer;
import com.CedarDefinitionalImplementation.log.Logger;
import com.CedarDefinitionalImplementation.log.LogTag;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.NullNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import java.util.Optional;


/**
 * DefinitionalEngine
 */
public class DefinitionalEngine {
    private ObjectMapper mapper;

    public DefinitionalEngine() {
        this.mapper = new ObjectMapper();
    }

    /**
     * Authorization query.
     *
     * @param json JSON string containing Query and Slice, using the serde
     * serialization of the corresponding Rust objects.
     * @return JSON string containing Response
     */
    public String isAuthorized_str(String json) {
	    Timer<Optional<difftest_mhelpers.Json>> query = new Timer<>(() -> deserializeQuery(json));
	    Logger.get().set(LogTag.Deserialization, query);
	    return query.get().map(x -> isAuthorized_json(x)).orElse("null");
    }


    private Optional<difftest_mhelpers.Json> deserializeQuery(String json) { 
	    try { 
		    JsonNode js = mapper.readTree(json);
		    return Optional.of(DafnyUtils.convertJsonJacksonToDafny(js));
	    } catch (JsonProcessingException e) { 
		    return Optional.empty();
	    }

    }

    /**
     * Authorization query.
     *
     * @param json JsonNode containing Query and Slice, using the Rust AST
     * form of the JSON, not the official interchange format.
     * @return JsonNode containing Response
     */
    public String isAuthorized_json(difftest_mhelpers.Json json) {
	    try { 
		    Timer<difftest_mhelpers.Json> authResult = new Timer<>(() -> difftest_mmain.__default.isAuthorizedJson(json));
		    Logger.get().set(LogTag.Auth, authResult);
		    Timer<JsonNode> serialResult = new Timer<>(() -> DafnyUtils.convertJsonDafnyToJackson(authResult.get()));
		    Logger.get().set(LogTag.Serialization, serialResult);
		    ObjectNode topLevel = mapper.createObjectNode();
		    for (LogTag tag : LogTag.iter()) { 
			    topLevel.put(tag.toString(), Logger.get().get(tag));
		    }
		    topLevel.set("response", serialResult.get());
		    return mapper.writeValueAsString(topLevel);
	    } catch (JsonProcessingException e) { 
		    return "null";
	    }
    }

}
