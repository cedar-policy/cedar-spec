include "../def/all.dfy"
include "../validation/all.dfy"
include "helpers.dfy"

module difftest.main {
  // This module contains the entry points for differential testing for the
  // definitional engine (`isAuthorized`) and validator (`Validate`).

  import opened def.base
  import opened def.core
  import opened def.engine
  import opened def.std
  import opened def.templates
  import opened def.ext.fun
  import opened restrictedExpr
  import opened validation.types
  import opened validation.validator
  import opened helpers

  method responseToProdJson(r: Response, errs: set<string>) returns (ja: Json) {
    var errsSeq := setToSequenceUnordered(errs);
    var reasonSeq := setToSequenceUnordered(r.policies);
    return JsonObject(
        map[
          "decision" := JsonString(
            match r.decision {
              case Allow => "Allow"
              case Deny => "Deny"
            }),
          "diagnostics" := JsonObject(
            map[
              // The order is nondeterministic, but errors are currently ignored in
              // the differential-testing comparison
              "errors" := JsonArray(mapSeq((e: string) => JsonString(e), errsSeq)),
              // The order is nondeterministic, so we'll have to ignore order in the
              // differential-testing comparison
              "reason" := JsonArray(mapSeq((p: PolicyID) => JsonString(p.id), reasonSeq))
            ])
        ]);
  }

  const idFromProdJson := stringDeserializer(s => Ok(Id(s)));

  const nameFromProdJson :=
    objDeserializer2Fields(
      "path", seqDeserializer(idFromProdJson),
      "id", idFromProdJson,
      (tyPathIds, tyId) => Ok(Name(tyId, tyPathIds)));

  const entitytypeFromProdJson :=
    sumDeserializer(
      map[
        "Concrete" := j => var n :- nameFromProdJson(j); Ok(EntityType(n)),
        "Unspecified" := _ => Ok(EntityType.UNSPECIFIED)
      ]);

  const entityUIDFromProdJson :=
    objDeserializer2Fields(
      "ty", entitytypeFromProdJson,
      "eid", getJsonString,
      (et, eid) => Ok(EntityUID.EntityUID(et, eid)));

  const binaryOpFromProdJson :=
    enumDeserializer(
      map[
        "Eq" := BinaryOp.Eq,
        "Less" := Less,
        "LessEq" := LessEq,
        "In" := BinaryOp.In,
        "Contains" := Contains,
        "ContainsAll" := ContainsAll,
        "ContainsAny" := ContainsAny,
        "Add" := Add,
        "Sub" := Sub
      ]);

  const unaryOpFromProdJson :=
    enumDeserializer(
      map[
        "Not" := Not,
        "Neg" := Neg
      ]);

  const extFuncOpFromProdJson :=
    objDeserializer1Field(
      "function_name", nameFromProdJson,
      name => Ok(name));

  function exprFromProdJson(j: Json): FromProdResult<Expr> {
    var jkind :- getJsonField(j, "expr_kind");
    var exprFromProdJsonRec := jr requires jr < jkind => exprFromProdJson(jr);
    var (tag, body) :- unpackJsonSum(jkind);
    match tag {
      case "Lit" =>
        var prim :- deserializeSum(
                      body,
                      map[
                        "Bool" := boolDeserializer(b => Ok(Primitive.Bool(b))),
                        "Long" := intDeserializer(i => Ok(Primitive.Int(i))),
                        "String" := stringDeserializer(s => Ok(Primitive.String(s))),
                        "EntityUID" := bodyDeserializer(entityUIDFromProdJson,
                                                        uid => Ok(Primitive.EntityUID(uid)))
                      ]);
        Ok(PrimitiveLit(prim))
      case "Var" =>
        var theVar :- deserializeEnum(
                        body,
                        map[
                          "principal" := Var.Principal,
                          "action" := Action,
                          "resource" := Var.Resource,
                          "context" := Context
                        ]);
        Ok(Var(theVar))
      case "If" =>
        var cond :- deserializeField(body, "test_expr", exprFromProdJsonRec);
        var ethen :- deserializeField(body, "then_expr", exprFromProdJsonRec);
        var eelse :- deserializeField(body, "else_expr", exprFromProdJsonRec);
        Ok(If(cond, ethen, eelse))
      case "And" =>
        var left :- deserializeField(body, "left", exprFromProdJsonRec);
        var right :- deserializeField(body, "right", exprFromProdJsonRec);
        Ok(And(left, right))
      case "Or" =>
        var left :- deserializeField(body, "left", exprFromProdJsonRec);
        var right :- deserializeField(body, "right", exprFromProdJsonRec);
        Ok(Or(left, right))
      case "UnaryApp" =>
        var op :- deserializeField(body, "op", unaryOpFromProdJson);
        var arg :- deserializeField(body, "arg", exprFromProdJsonRec);
        Ok(UnaryApp(op, arg))
      case "BinaryApp" =>
        var op :- deserializeField(body, "op", binaryOpFromProdJson);
        var arg1 :- deserializeField(body, "arg1", exprFromProdJsonRec);
        var arg2 :- deserializeField(body, "arg2", exprFromProdJsonRec);
        Ok(BinaryApp(op, arg1, arg2))
      case "MulByConst" =>
        var arg :- deserializeField(body, "arg", exprFromProdJsonRec);
        var cons :- deserializeField(body, "constant", getJsonInt);
        Ok(UnaryApp(MulBy(cons), arg))
      case "ExtensionFunctionApp" =>
        var name :- deserializeField(body, "op", extFuncOpFromProdJson);
        var jargs :- getJsonField(body, "args");
        var args :- deserializeSeq(jargs, exprFromProdJsonRec);
        Ok(Expr.Call(name, args))
      case "GetAttr" =>
        var expr :- deserializeField(body, "expr", exprFromProdJsonRec);
        var attr :- deserializeField(body, "attr", getJsonString);
        Ok(GetAttr(expr, attr))
      case "HasAttr" =>
        var expr :- deserializeField(body, "expr", exprFromProdJsonRec);
        var attr :- deserializeField(body, "attr", getJsonString);
        Ok(HasAttr(expr, attr))
      case "Like" =>
        var expr :- deserializeField(body, "expr", exprFromProdJsonRec);
        var pat :- deserializeField(body, "pattern", patternFromProdJson);
        Ok(UnaryApp(Like(pat), expr))
      case "Set" =>
        var exprs :- deserializeSeq(body, exprFromProdJsonRec);
        Ok(Expr.Set(exprs))
      case "Record" =>
        var list :- getJsonField(body, "pairs");
        var pairs :- deserializeSeq(
                       list,
                       ja requires ja < list =>
                         deserializeTuple2Elts(
                           ja,
                           getJsonString,
                           exprFromProdJsonRec,
                           (attr, expr) => Ok((attr, expr))));
        Ok(Expr.Record(pairs))
      case _ => Err({UnexpectedFromProdErr("expr case " + tag)})
    }
  }

  // https://github.com/dafny-lang/dafny/issues/3814 would let us write `u is char` instead.
  predicate isChar(u: int) {
    0 <= u < 0xD800 || 0xE000 <= u <= 0x10_FFFF
  }

  const patElemFromProdJson :=
    sumDeserializer(
      map[
        "Char" := intDeserializer(
          u =>
            if isChar(u)
            then
              Ok(JustChar(u as char))
            else
              Err({UnexpectedFromProdErr("Unicode value out of valid range")})),
        "Wildcard" := _ => Ok(Star)
      ]);

  const patternFromProdJson := seqDeserializer(patElemFromProdJson);

  // Deserializers for datatypes where the definitional version contains the
  // SlotId and the production one doesn't, so we need outside knowledge of the
  // SlotId to use. Group them in a datatype to save the boilerplate of passing
  // along the `slotId` parameter explicitly.
  datatype ScopeDeserializers = ScopeDeserializers(slotId: SlotId) {
    const entityUIDOrSlotFromProdJson :=
      sumDeserializer(
        map[
          "EUID" := bodyDeserializer(entityUIDFromProdJson, e => Ok(EntityUIDOrSlot.EntityUID(e))),
          // The temporary variable is needed to work around a verification issue,
          // probably https://github.com/dafny-lang/dafny/issues/2083.
          "Slot" := (var d := _ => Ok(EntityUIDOrSlot.Slot(slotId)); d)
        ]);

    // Corresponds to production `PrincipalOrResourceConstraint`.
    const scopeTemplateFromProdJson :=
      sumDeserializer(
        map[
          "Any" := _ => Ok(ScopeTemplate.Any),
          "In" := bodyDeserializer(entityUIDOrSlotFromProdJson, e => Ok(ScopeTemplate.In(e))),
          "Eq" := bodyDeserializer(entityUIDOrSlotFromProdJson, e => Ok(ScopeTemplate.Eq(e)))
        ]);
  }

  // Corresponds to production `ActionConstraint`.
  const actionScopeFromProdJson :=
    sumDeserializer(
      map[
        "Any" := _ => Ok(ActionScope(Scope.Any)),
        "In" := bodyDeserializer(seqDeserializer(entityUIDFromProdJson), es => Ok(ActionInAny(es))),
        "Eq" := bodyDeserializer(entityUIDFromProdJson, e => Ok(ActionScope(Scope.Eq(e))))
      ]);

  const policyTemplateFromProdJson :=
    objDeserializer5Fields(
      "effect", enumDeserializer(map[
                                   "permit" := Permit,
                                   "forbid" := Forbid
                                 ]),
      "principal_constraint", objDeserializer1Field(
        "constraint", ScopeDeserializers("?principal").scopeTemplateFromProdJson,
        s => Ok(PrincipalScopeTemplate(s))),
      "action_constraint", actionScopeFromProdJson,
      "resource_constraint", objDeserializer1Field(
        "constraint", ScopeDeserializers("?resource").scopeTemplateFromProdJson,
        s => Ok(ResourceScopeTemplate(s))),
      "non_head_constraints", exprFromProdJson,
      (effect, pScope, aScope, rScope, cond) => Ok(PolicyTemplate(effect, pScope, aScope, rScope, cond))
    );

  function attrsFromProdJsonObject(j: Json): FromProdResult<map<Attr, Value>> {
    var attr_keys :- getJsonObject(j);
    var expr_vals :- mapMapValuesFromProd(exprFromProdJson, attr_keys);
    var value_vals :- mapMapValuesFromProd(exprToValue, expr_vals);
    Ok(value_vals)
  }

  // In the production engine, `EntityUIDEntry` is the data type for a request
  // field that is either a "concrete" EntityUID or "unknown" (for partial
  // evaluation). We currently don't support partial evaluation, so we just
  // translate the "concrete" variant to an EntityUID.
  const entityUIDEntryFromProdJson :=
    sumDeserializer(map["Concrete" := entityUIDFromProdJson]);

  function getEntityUIDEntryField(request: Json, f: string): FromProdResult<EntityUID> {
    deserializeField(request, f, entityUIDEntryFromProdJson)
  }

  const entityEntryFromProdJson :=
    tupleDeserializer2Elts(
      entityUIDFromProdJson,
      objDeserializer2Fields(
        "attrs", attrsFromProdJsonObject,
        "ancestors", setDeserializer(entityUIDFromProdJson),
        (attrs, ancestors) => Ok(EntityData(attrs, ancestors))
      ),
      (uid, edata) => Ok((uid, edata))
    );

  function exprToValue(expr: Expr): FromProdResult<Value> {
    match evaluate(expr) {
      case Some(v) => Ok(v)
      case None => Err({UnexpectedFromProdErr("Attribute values must be restricted expressions")})
    }
  }

  function buildContext(context_field: Json): FromProdResult<Record> {
    var as_expr :- exprFromProdJson(context_field);
    var value :- exprToValue(as_expr);
    match value {
      case Record(rcd) => Ok(rcd)
      case _ => Err({UnexpectedFromProdErr("Context must be a record")})
    }
  }

  const templateLinkedPolicyFromProdJson :=
    objDeserializer2Fields(
      "template_id", stringDeserializer(s => Ok(PolicyTemplateID(s))),
      "values", mapDeserializer(entityUIDFromProdJson),
      (tid, slotEnv) => Ok(TemplateLinkedPolicy(tid, slotEnv))
    );

  const policyStoreFromProdJson :=
    objDeserializer2Fields(
      "templates", jtemplates => (
          var templates :- getJsonObject(jtemplates);
          var templates1 :- mapMapValuesFromProd(policyTemplateFromProdJson, templates);
          Ok(mapMapKeys(s => PolicyTemplateID(s), templates1))
        ),
      "links", jlinkedPolicies => (
          var linkedPolicies :- getJsonObject(jlinkedPolicies);
          var linkedPolicies1 :- mapMapValuesFromProd(templateLinkedPolicyFromProdJson, linkedPolicies);
          Ok(mapMapKeys(s => PolicyID(s), linkedPolicies1))
        ),
      (templates, linkedPolicies) => (
          var policyStore := TemplatedPolicyStore(templates, linkedPolicies);
          if policyStore.isValid()
          then Ok(linkPolicyStore(policyStore))
          else Err({UnexpectedFromProdErr("Invalid policy template link(s)")})
        )
    );

  const authorizerFromProdJson :=
    objDeserializer3Fields(
      "request", jrequest => (
          var principal :- getEntityUIDEntryField(jrequest, "principal");
          var action :- getEntityUIDEntryField(jrequest, "action");
          var resource :- getEntityUIDEntryField(jrequest, "resource");
          // Note: In the production engine, the `context` field is wrapped in an
          // `Option` that can be `None` for partial evaluation. But currently, for
          // differential testing, the `context` is always `Some`, and the default
          // Serde JSON serialization of `Some(x)` is just that of `x` without an
          // explicit representation of the `Option` layer, so we don't have to do
          // anything additional here.
          var context :- deserializeField(jrequest, "context", buildContext);
          Ok(Request(principal, action, resource, context))
        ),
      "entities", jentities => (
          var entities :- deserializeField(jentities, "entities", seqDeserializer(entityEntryFromProdJson));
          var entitiesMap :- mapFromEntriesProd(entities);
          Ok(EntityStore(entitiesMap))
        ),
      "policies", jpolicySet => policyStoreFromProdJson(jpolicySet),
      (request, entityStore, policyStore) =>
        Ok(Authorizer(request, Store(entityStore, policyStore)))
    );

  function isAuthorizedJson1(request: Json): FromProdResult<Response> {
    var authorizer :- authorizerFromProdJson(request);
    Ok(authorizer.isAuthorized())
  }

  // Main differential-testing entry point: receives Json and responds in Json
  method isAuthorizedJson(request: Json) returns (response: Json) {
    var answer := isAuthorizedJson1(request);
    var ansAndErrors := match answer {
      case Ok(ans) => (ans, {})
      case Err(errs) =>
        (Response(Deny, {}), set e | e in errs :: e.desc)
    };
    response := responseToProdJson(ansAndErrors.0, ansAndErrors.1);
  }

  // Note: the types we have to support here are limited to those allowed in
  // the Rust SchemaFileFormat, which is more restrictive than our Schema type
  function typeFromProdJson(j: Json): FromProdResult<Type> {
    var typeFromProdJsonRec := jr requires jr < j => typeFromProdJson(jr);
    var attrTypesFromProdJsonObjectRec := jr requires jr < j => attrTypesFromProdJsonObject(jr);
    var (tag, body) :- unpackJsonSum(j);
    match tag {
      case "Primitive" =>
        var ty1 :- getJsonField(body, "primitiveType");
        var ty :- deserializeEnum(
                    ty1,
                    map[
                      "Bool" := Type.Bool(AnyBool),
                      "Long" := Type.Int,
                      "String" := Type.String
                    ]);
        Ok(ty)
      case "Set" =>
        var inner :- deserializeField(body, "elementType", typeFromProdJsonRec);
        Ok(Type.Set(inner))
      case "EntityOrRecord" =>
        var (tag1, body1) :- unpackJsonSum(body);
        match tag1 {
          case "Record" =>
            var attrs :- getJsonField(body1, "attrs");
            var attrs1 :- deserializeField(attrs, "attrs", attrTypesFromProdJsonObjectRec);
            Ok(Type.Record(attrs1))
          case "Entity" =>
            var lub :- deserializeField(body1, "lub_elements", setDeserializer(nameFromProdJson));
            Ok(Type.Entity(EntityLUB(set e <- lub :: EntityType(e))))
          case _ => Err({UnexpectedFromProdErr("EntityOrRecord case " + tag)})
        }
      case "ExtensionType" =>
        var name :- deserializeField(body, "name", nameFromProdJson);
        Ok(Type.Extension(name))
      case _ => Err({UnexpectedFromProdErr("Type case " + tag)})
    }
  }

  function attrtypeFromProdJson(j: Json): FromProdResult<AttrType> {
    var typeFromProdJsonRec := jr requires jr < j => typeFromProdJson(jr);
    var attrType :- deserializeField(j, "attrType", typeFromProdJsonRec);
    var isRequired :- deserializeField(j, "isRequired", getJsonBool);
    Ok(AttrType(attrType,isRequired))
  }

  function attrTypesFromProdJsonObject(j: Json): FromProdResult<map<Attr, AttrType>> {
    var attrtypeFromProdJsonRec := jr requires jr < j => attrtypeFromProdJson(jr);
    deserializeMap(j, attrtypeFromProdJsonRec)
  }

  function entityTypePairFromProdJson(j: Json): FromProdResult<(EntityType, TypecheckerEntityType)> {
    deserializeTuple2Elts(
      j,
      nameFromProdJson,
      data => (
          var descendants :- deserializeField(data, "descendants", setDeserializer(nameFromProdJson));
          var descendants1 := set e <- descendants :: EntityType(e);
          var attrs :- getJsonField(data, "attributes");
          var attrs1 :- deserializeField(attrs, "attrs", attrTypesFromProdJsonObject);
          Ok(TypecheckerEntityType(descendants1, attrs1))
        ),
      (ty, et) => Ok((EntityType(ty), et))
    )
  }

  const entitytypeFromProdJsonOption :=
    sumDeserializer(
      map[
        "Concrete" := j => var n :- nameFromProdJson(j); Ok(Some(EntityType(n))),
        "Unspecified" := _ => Ok(None)
      ]);

  function applySpecFromProdJson(j: Json): FromProdResult<TypecheckerApplySpec> {
    var pas :- deserializeField(j, "principalApplySpec", setDeserializer(entitytypeFromProdJsonOption));
    var ras :- deserializeField(j, "resourceApplySpec", setDeserializer(entitytypeFromProdJsonOption));
    Ok(TypecheckerApplySpec(pas,ras))
  }

  function actionIdPairFromProdJson(j: Json): FromProdResult<(EntityUID, TypecheckerActionId)> {
    deserializeTuple2Elts(
      j,
      entityUIDFromProdJson,
      data => (
          var appliesTo :- deserializeField(data, "appliesTo", applySpecFromProdJson);
          var descendants :- deserializeField(data, "descendants", setDeserializer(entityUIDFromProdJson));
          var context :- getJsonField(data, "context");
          var context1 :- deserializeField(context, "attrs", attrTypesFromProdJsonObject);
          Ok(TypecheckerActionId(appliesTo, descendants, context1))
        ),
      (uid, act) => Ok((uid, act))
    )
  }

  const validatorFromProdJson :=
    objDeserializer2Fields(
      "policies", jpolicies => policyStoreFromProdJson(jpolicies),
      "schema", jschema => (
          var entityTypes :- deserializeField(jschema, "entityTypes", seqDeserializer(entityTypePairFromProdJson));
          var entityTypesMap :- mapFromEntriesProd(entityTypes);
          var actionIds :- deserializeField(jschema, "actionIds", seqDeserializer(actionIdPairFromProdJson));
          var actionIdsMap :- mapFromEntriesProd(actionIds);
          Ok(Schema(entityTypesMap, actionIdsMap))
        ),
      (policyStore, schema) => Ok((policyStore,Validator(schema)))
    );

  method validateJson1(request: Json) returns (res: FromProdResult<seq<TypeError>>) {
    var policyStoreAndValidator :- validatorFromProdJson(request);
    var errs := policyStoreAndValidator.1.Validate(policyStoreAndValidator.0);
    return Ok(errs);
  }

  function typeErrorToString(e: TypeError): string {
    match e {
      case LubErr(_,_) => "LubErr"
      case SubtyErr(_,_) => "SubtyErr"
      case UnexpectedType(_) => "UnexpectedType"
      case AttrNotFound(_,_) => "AttrNotFound"
      case UnknownEntities(_) => "UnknownEntities"
      case ExtensionErr(_) => "ExtensionErr"
      case EmptyLUB => "EmptyLUB"
      case AllFalse => "AllFalse"
    }
  }

  method validationResToProdJson(errs: seq<TypeError>, parseErrs: set<string>) returns (ja: Json) {
    var parseErrsSeq := setToSequenceUnordered(parseErrs);
    return JsonObject(
        map[
          "validationErrors" := JsonArray(mapSeq((e: TypeError) => JsonString(typeErrorToString(e)), errs)),
          "parseErrors" := JsonArray(mapSeq((e: string) => JsonString(e), parseErrsSeq))
        ]);
  }

  // Differential testing entry point for validation
  method validateJson(request: Json) returns (response: Json) {
    var res := validateJson1(request);
    var resAndErrors := match res {
      case Ok(res1) => (res1, {})
      case Err(errs) => ([], set e | e in errs :: e.desc
      )};
    response := validationResToProdJson(resAndErrors.0, resAndErrors.1);
  }
}

module difftest.restrictedExpr {
  import opened def.core
  import opened def.base
  import ext = def.ext.fun
  import opened def.engine
  import opened def.std

  export
    provides
      evaluate,
      std,
      core

  function evaluate(e: Expr): Option<Value>
  {
    match e {
      case PrimitiveLit(l) => Some(Primitive(l))
      case Record(r) =>
        var r' :- evaluateRecord(r);
        Some(Value.Record(r'))
      case Set(s) =>
        var s' :- evaluateSet(s);
        Some(Value.Set(s'))
      case Call(name, args) =>
        var vs :- evaluateSeq(args);
        match Evaluator.applyExtFun(name, vs) {
          case Ok(v) => Some(v)
          case Err(_) => None
        }
      case _ => None
    }
  }

  function evaluateRecord(m: seq<(Attr, Expr)>): Option<map<Attr,Value>>
  {
    if |m| == 0 then Some(map[])
    else
      var attr := m[0].0;
      var v :- evaluate(m[0].1);
      var vs :- evaluateRecord(m[1..]);
      Some(vs[attr := v])
  }

  function evaluateSet(es: seq<Expr>): Option<set<Value>>
  {
    if |es| == 0 then Some({})
    else
      var v :- evaluate(es[0]);
      var vs :- evaluateSet(es[1..]);
      Some({v}+vs)
  }

  function evaluateSeq(es: seq<Expr>): Option<seq<Value>>
  {
    if |es| == 0 then Some([])
    else
      var v :- evaluate(es[0]);
      var vs :- evaluateSeq(es[1..]);
      Some([v]+vs)
  }
}
