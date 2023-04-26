package com.CedarDefinitionalImplementation;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.math.BigInteger;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.BooleanNode;
import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import com.fasterxml.jackson.databind.node.BigIntegerNode;
import com.fasterxml.jackson.databind.node.NullNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import com.fasterxml.jackson.databind.node.TextNode;

// TODO: Look into whether using an approach similar to ValueDeserializer might
// be cleaner?
public class DafnyUtils {
    public static difftest_mhelpers_Compile.Json convertJsonJacksonToDafny(JsonNode node) {
        switch (node.getNodeType()) {
            case NULL:
                return difftest_mhelpers_Compile.Json.create_JsonNull();
            case BOOLEAN:
                return difftest_mhelpers_Compile.Json.create_JsonBool(node.asBoolean());
            case NUMBER:
                if (!node.canConvertToExactIntegral())
                    throw new UnsupportedOperationException("Non-integer Jackson number is not supported by Dafny yet");
                else if (!node.canConvertToLong())
                    throw new UnsupportedOperationException("Jackson integer is too big for Java long");
                else
                    return difftest_mhelpers_Compile.Json.create_JsonInt(BigInteger.valueOf(node.asLong()));
            case STRING:
                // Dafny currently doesn't offer an official API to convert
                // between a Java `String` and a `DafnySequence<CodePoint>`
                // representing a Dafny unicode `string`. The functions
                // `asUnicodeString` and `verbatimString` (used in
                // `convertJsonDafnyToJackson` below) work as of this writing
                // but may break at any time. If and when they break, our tests
                // will detect the problem and we'll just copy the code of the
                // working versions then. See
                // https://github.com/dafny-lang/libraries/issues/73#issuecomment-1503247487.
                return difftest_mhelpers_Compile.Json.create_JsonString(
                    dafny.DafnySequence.asUnicodeString(node.asText()));
            case ARRAY:
                difftest_mhelpers_Compile.Json dafnyElements[] = new difftest_mhelpers_Compile.Json[node.size()];
                for (int i = 0; i < node.size(); i++)
                    dafnyElements[i] = convertJsonJacksonToDafny(node.get(i));
                return difftest_mhelpers_Compile.Json.create_JsonArray(
                    dafny.DafnySequence.of(difftest_mhelpers_Compile.Json._typeDescriptor(), dafnyElements));
            case OBJECT:
                HashMap<dafny.DafnySequence<dafny.CodePoint>, difftest_mhelpers_Compile.Json> mapForDafny = new HashMap<>();
                Iterator<Map.Entry<String, JsonNode>> fieldsIter = node.fields();
                while (fieldsIter.hasNext()) {
                    Map.Entry<String, JsonNode> entry = fieldsIter.next();
                    mapForDafny.put(dafny.DafnySequence.asUnicodeString(entry.getKey()), convertJsonJacksonToDafny(entry.getValue()));
                }
                return difftest_mhelpers_Compile.Json.create_JsonObject(new dafny.DafnyMap<>(mapForDafny));
            default:
                throw new UnsupportedOperationException("Unsupported Jackson JsonNode type: " + node.getNodeType());
        }
    }

    public static JsonNode convertJsonDafnyToJackson(difftest_mhelpers_Compile.Json node) {
        if (node.is_JsonNull()) {
            return NullNode.instance;
        } else if (node.is_JsonBool()) {
            return BooleanNode.valueOf(node.dtor_b());
        } else if (node.is_JsonInt()) {
            return BigIntegerNode.valueOf(node.dtor_i());
        } else if (node.is_JsonString()) {
            return TextNode.valueOf(node.dtor_s().verbatimString());
        } else if (node.is_JsonArray()) {
            ArrayNode jacksonNode = new ArrayNode(JsonNodeFactory.instance);
            for (difftest_mhelpers_Compile.Json item : node.dtor_a()) {
                jacksonNode.add(convertJsonDafnyToJackson(item));
            }
            return jacksonNode;
        } else if (node.is_JsonObject()) {
            ObjectNode jacksonNode = new ObjectNode(JsonNodeFactory.instance);
            for (dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, difftest_mhelpers_Compile.Json> dafnyEntry : node.dtor_o().
                <dafny.DafnySequence<? extends dafny.CodePoint>, difftest_mhelpers_Compile.Json>entrySet().Elements()) {
                jacksonNode.set(dafnyEntry.dtor__0().verbatimString(),
                    convertJsonDafnyToJackson(dafnyEntry.dtor__1()));
            }
            return jacksonNode;
        } else {
            throw new AssertionError("Dafny Json is not one of the known types");
        }
    }
}
