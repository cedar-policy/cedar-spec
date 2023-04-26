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
 * DefinitionalValidator
 */
public class DefinitionalValidator {
    private ObjectMapper mapper;

    public DefinitionalValidator() {
        this.mapper = new ObjectMapper();
    }

    /**
     * Validation query.
     *
     * @param json JSON string containing Schema and Policy, using the serde
     * serialization of the corresponding Rust objects.
     * @return JSON string containing validation result
     */
    public String validate_str(String json) {
	    Timer<Optional<difftest_mhelpers_Compile.Json>> query = new Timer<>(() -> deserializeQuery(json));
	    Logger.get().set(LogTag.Deserialization, query);
	    return query.get().map(x -> validate_json(x)).orElse("null");
    }

    private Optional<difftest_mhelpers_Compile.Json> deserializeQuery(String json) { 
	    try { 
		    JsonNode js = mapper.readTree(json);
		    return Optional.of(DafnyUtils.convertJsonJacksonToDafny(js));
	    } catch (JsonProcessingException e) { 
		    return Optional.empty();
	    }

    }

    /**
     * Validation query.
     *
     * @param json JsonNode containing Schema and Policy, using the Rust AST
     * form of the JSON, not the official interchange format.
     * @return JsonNode containing validation result
     */
    public String validate_json(difftest_mhelpers_Compile.Json json) {
	    try { 
		    Timer<difftest_mhelpers_Compile.Json> valResult = new Timer<>(() -> difftest_mmain_Compile.__default.validateJson(json));
		    Logger.get().set(LogTag.Validation, valResult);
		    Timer<JsonNode> serialResult = new Timer<>(() -> DafnyUtils.convertJsonDafnyToJackson(valResult.get()));
		    Logger.get().set(LogTag.Serialization, serialResult);
		    ObjectNode topLevel = mapper.createObjectNode();
		    for (LogTag tag : LogTag.iter()) { 
			    topLevel.put(tag.toString(), Logger.get().get(tag));
		    }
		    topLevel.set("answer", serialResult.get());
		    return mapper.writeValueAsString(topLevel);
	    } catch (JsonProcessingException e) { 
		    return "null";
	    }
    }
}
