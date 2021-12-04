using Microsoft.Dafny;
using System;
using System.Collections.Generic;
using Token = Microsoft.Boogie.Token;

namespace DafnyPipeline {

  public class Lattice {
    //public Dictionary<HashSet<string>, string> InvLowMap { 
    //  get {
    //    defineLowInverse();
    //    return invLowMap;
    //  } 
    //}

    public Dictionary<string, HashSet<string>> highMap = new();
    public Dictionary<string, HashSet<string>> lowMap = new();
    // Create a dictionary that uses the hashset comparer, which compares items in the set for equality
    public Dictionary<HashSet<string>, string> invHighMap = new(HashSet<string>.CreateSetComparer());
    public Dictionary<HashSet<string>, string> invLowMap = new(HashSet<string>.CreateSetComparer());

    public void AddHighMap(string key, HashSet<string> value) {
      highMap.Add(key, value);
      invHighMap.Add(value, key);
      // Update low map
      foreach (string val in value) {
        if (lowMap.ContainsKey(val)) {
          var setMap = lowMap.GetValueOrDefault(val);
          setMap.Add(key);
        } else {
          lowMap.Add(val, new HashSet<string>() { key });
        }
      }
      defineLowInverse();
    }

    private void defineLowInverse() {
      // Clearing is an inefficient workaround to avoid duplicates. Should be fixed with IEquality comparers
      invLowMap.Clear();
      foreach(var item in lowMap) {
        invLowMap.TryAdd(item.Value, item.Key);
      }
    }



    private string HashSetToString(HashSet<string> set) {
      string retVal = "{ ";
      int numEls = set.Count;
      int i = 0;
      foreach (string val in set) {
        retVal += val;
        if (++i != numEls) {
          retVal += ", ";
        }
        
      }
      return retVal + " }";
    }

    public override string ToString() {
      string retVal = string.Empty;
      int indentSize = 4;
      int indentLvl = 0;
      retVal += new string(' ', indentSize * indentLvl) + "High Map:\n";
      indentLvl++;
      foreach (var pair in highMap) {
        retVal += new string(' ', indentSize * indentLvl);
        retVal += pair.Key + " --> " + HashSetToString(pair.Value) + "\n";
      }
      indentLvl--;
      retVal += new string(' ', indentSize * indentLvl) + "Low Map:\n";
      indentLvl++;
      foreach (var pair in lowMap) {
        retVal += new string(' ', indentSize * indentLvl);
        retVal += pair.Key + " --> " + HashSetToString(pair.Value) + "\n";
      }
      indentLvl--;
      retVal += new string(' ', indentSize * indentLvl) + "Inverse High Map:\n";
      indentLvl++;
      foreach (var pair in invHighMap) {
        retVal += new string(' ', indentSize * indentLvl);
        retVal += HashSetToString(pair.Key) + " --> " + pair.Value + "\n";
      }
      indentLvl--;
      retVal += new string(' ', indentSize * indentLvl) + "Inverse Low Map:\n";
      indentLvl++;
      foreach (var pair in invLowMap) {
        retVal += new string(' ', indentSize * indentLvl);
        retVal += HashSetToString(pair.Key) + " --> " + pair.Value + "\n";
      }
      return retVal;
    }
  }


  public class InformationFlowState {
    public HashSet<string> Global;
    public Dictionary<string, InformationFlowVar> Vars;
    public Dictionary<string, HashSet<string>> Ctrl;
    public int labelNum { get; set; }
    public List<Statement> parentStmtList { get; internal set; }
    public List<MemberDecl> currentClassMembers { get; internal set; }
    public bool addAssertions { get; internal set; }

    public List<string> localVars;
    public List<Method> methods;
    internal List<Function> funcs;
    internal Method parentMethod;
    internal bool prevCAS;
    internal BinaryExpr casInvariant;

    public InformationFlowState() {
      labelNum = 0;
      localVars = new List<string>();
      Global = new HashSet<string>();
      Ctrl = new Dictionary<string, HashSet<string>>();
      Vars = new Dictionary<string, InformationFlowVar>();
      methods = new List<Method>();
      funcs = new List<Function>();
      prevCAS = false;
    }
  }

  public class InformationFlowVar {
    private Field variable;

    public Field securityLevel { get; set; }
    public Function securityClassification { get; set; }
    public Field Variable {
      get { return variable; }
      internal set {
        variable = value;
        varType = value.Type;
      }
    }
    public string name { get; }
    public bool isGlobal { get; private set; }
    public Microsoft.Dafny.Type varType { get; set; }

    public InformationFlowVar(Field variable, bool isGlobal = true) {
      this.isGlobal = isGlobal;
      this.variable = variable;
      name = variable.Name;
      varType = variable.Type;
    }

    public InformationFlowVar(string name, bool isGlobal = true) {
      this.isGlobal = isGlobal;
      this.name = name;
    }


  }

  public class InformationFlowException : Exception {
    public InformationFlowException() {
    }

    public InformationFlowException(string message)
        : base(message) {
    }

    public InformationFlowException(string message, Exception inner)
        : base(message, inner) {
    }
  }

  // Look at SyntaxTreeVisitor.cs? Double Dispatch would be nice, but AST needs to be modified for that

  public class InformationFlowVisitor {
    Program program;
    List<TopLevelDecl> topDecls;
    Microsoft.Dafny.Type latticeType;
    Microsoft.Dafny.Type secType;
    InformationFlowState currentState;
    ErrorReporter reporter;
    DefaultClassDecl defaultClass;
    public Lattice userLattice;

    private int numSecLevels = 0;
    private List<TypeParameter> emptyTypeArgs = new List<TypeParameter>();
    private List<Formal> defaultFormals = new List<Formal>();
    private List<AttributedExpression> defaultRequires = new List<AttributedExpression>();
    private List<FrameExpression> defaultReads = new List<FrameExpression>();
    private List<AttributedExpression> defaultEnsures = new List<AttributedExpression>();
    //private readonly Specification<Expression> defaultDecreases = new Specification<Expression>(new List<Expression>(), null);
    private Specification<FrameExpression> defaultModifies = new Specification<FrameExpression>(new List<FrameExpression>(), null);
    private ConstantField latticeDef;
    private Expression highestSec;
    private Expression lowestSec;

    public InformationFlowVisitor(Program prog) {
      this.program = prog;
      this.reporter = prog.reporter;
      this.topDecls = program.DefaultModuleDef.TopLevelDecls;
      // Default class always exists, so this is valid
      this.defaultClass = (DefaultClassDecl)prog.DefaultModuleDef.TopLevelDecls.Find(x => x.Name == "_default");
      currentState = new InformationFlowState();
      highestSec = nameSeg("HIGHEST_SEC");
      lowestSec = nameSeg("LOWEST_SEC");
    }

    // Util function to create NameSegments quickly
    private NameSegment nameSeg(string name, List<Microsoft.Dafny.Type> typeArgs = null) {
      return new NameSegment(Token.NoToken, name, typeArgs);
    }

    public void Init(bool addAssertions) {
      currentState.addAssertions = addAssertions;
      // Empty program, but the "_default" class is defined as a top level decl
      if (defaultClass.Members.Count == 0 && program.DefaultModuleDef.Includes.Count == 0 && program.DefaultModuleDef.TopLevelDecls.Count == 1) {
        // Boilerplate will be added anyway, but add an empty class for the user to fill out
        topDecls.Add(new ClassDecl(Token.NoToken, "YourClass", program.DefaultModuleDef, emptyTypeArgs, new List<MemberDecl>(), null, false, null));
      }

      DefineSec();
      DefineLatticeType();
      DefineSecAttack();
      AddLatticeDefinition();
      if (!defaultClass.Members.Exists(x => x.Name == "CAS")) {
        DefineCAS();
      }
      if (!defaultClass.Members.Exists(x => x.Name == "order")) {
        DefinePartialOrderOperator();
      }

      try {
        Visit(program, ref currentState);
      } catch (InformationFlowException ife) {
        // Error during injection. Try re-running the initialiser
        //ife.

      }
      
    }

    private void DefineSecAttack() {
      if (!defaultClass.Members.Exists(x => x.Name == "secAttack")) {
        ConstantField secAttack = new ConstantField(Token.NoToken, "secAttack", nameSeg("Low"), false, false, secType, null);
        defaultClass.Members.Insert(0, secAttack);
      }
    }

    private void AddLatticeDefinition() {
      if (!defaultClass.Members.Exists(x=>x.Name == "lattice")) {
        // If not defined, use a default of a binary lattice
        List<ExpressionPair> defaultBinaryLattice = new List<ExpressionPair>() {
          new ExpressionPair(nameSeg("Low"), new SetDisplayExpr(Token.NoToken, true, new List<Expression>(){ nameSeg("Low"),  nameSeg("High") })),
          new ExpressionPair(nameSeg("High"), new SetDisplayExpr(Token.NoToken, true, new List<Expression>(){ nameSeg("High") }))
        };
        var latticeDef = new ConstantField(Token.NoToken, "lattice", new MapDisplayExpr(Token.NoToken, true, defaultBinaryLattice), false, false, latticeType, null);
        // Insert near the top after Lattice definition
        defaultClass.Members.Add(latticeDef);
      }
      // Checking validity of lattice definition is done in phase 2 while adding assertions
    }

    private void DefineCAS() {
      //Create a CAS method of the form:
      //method CAS<T(==)> (x: T, e1: T, e2: T) returns(b: bool, x2: T)
      //  ensures x == e1 ==> x2 == e2 && b;
      //  ensures x != e1 ==> x2 == x && !b;
      //  {
      //   if (x == e1) {
      //     x2:= e2;
      //     b:= true;
      //   } else {
      //     x2:= x;
      //     b:= false;
      //    }
      //  }
      var generic = new TypeParameter(
        Token.NoToken,
        "T",
        TypeParameter.TPVarianceSyntax.NonVariant_Strict,
        new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.Required, Microsoft.Dafny.Type.AutoInitInfo.MaybeEmpty, false)
      );
      var genericType = new UserDefinedType(generic);
      // In params
      var x = nameSeg("x");
      var e1 = nameSeg("e1");
      var e2 = nameSeg("e2");
      // Out params
      var x2 = nameSeg("x2");
      var b = nameSeg("b");

      var ins = new List<Formal>() {
        new Formal(Token.NoToken, x.Name, genericType, true, false, null),
        new Formal(Token.NoToken, e1.Name, genericType, true, false, null),
        new Formal(Token.NoToken, e2.Name, genericType, true, false, null)
      };
      var outs = new List<Formal>() {
        new Formal(Token.NoToken, b.Name, new BoolType(), false, false, null),
        new Formal(Token.NoToken, x2.Name, genericType, false, false, null),
      };
      var bodyStmts = new List<Statement>() {
        new IfStmt(Token.NoToken, Token.NoToken, false,
          // Guard
          new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, x, e1),
          // Then
           new BlockStmt(Token.NoToken, Token.NoToken, new List<Statement>() {
             // x2 := e2
              new UpdateStmt(Token.NoToken, Token.NoToken, new List<Expression>(){ x2 }, new List<AssignmentRhs>{ new ExprRhs(e2) }), 
              // b := true
              new UpdateStmt(Token.NoToken, Token.NoToken, new List<Expression>(){ b }, new List<AssignmentRhs>{ new ExprRhs(new LiteralExpr(Token.NoToken, true)) })

            }),
           // Else
           new BlockStmt(Token.NoToken, Token.NoToken, new List<Statement>() {
             // x2 := x
              new UpdateStmt(Token.NoToken, Token.NoToken, new List<Expression>(){ x2 }, new List<AssignmentRhs>{ new ExprRhs(x) }), 
              // b := false
              new UpdateStmt(Token.NoToken, Token.NoToken, new List<Expression>(){ b }, new List<AssignmentRhs>{ new ExprRhs(new LiteralExpr(Token.NoToken, false)) })

            })
        )
      };
      var body = new BlockStmt(Token.NoToken, Token.NoToken, bodyStmts);
      var ensures = new List<AttributedExpression>() {
        new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp,
          new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, x, e1),
          new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, 
            new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, x2, e2), b
          ))
        ),
        new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp,
          new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, x, e1),
          new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, 
            new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, x2, x), 
            new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Not, b)
          ))
        )
      };
      var CAS = new Method(
        Token.NoToken,
        "CAS",
        false,
        false,
        new List<TypeParameter>() { generic },
        ins,
        outs,
        defaultRequires,
        defaultModifies,
        ensures,
        defaultDecreases(),
        body,
        null,
        null
      );

      DefaultClassDecl defaultClass = (DefaultClassDecl)topDecls.Find(x => x.Name == "_default");
      defaultClass.Members.Add(CAS);
    }

    private Specification<Expression> defaultDecreases() {
      return new Specification<Expression>(new List<Expression>(), null);
    }

    private void DefinePartialOrderOperator() {
      //Create a predicate of the form:
      //predicate order(l: Lattice, a: Sec, b: Sec)
      //{
      //    assume a in l && b in l;
      //        b in l[a]
      //}

      var a = nameSeg("a");
      var b = nameSeg("b");
      var l = nameSeg("l");
      //List<AttributedExpression> reqs = new List<AttributedExpression>()
      //{
      //  new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, a, l)),
      //  new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, b, l))
      //};
      var assumption = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And,
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, a, l),
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, b, l)
      );
      List<Formal> formals = new List<Formal>() {
            new Formal(Token.NoToken, l.Name, latticeType, true, false, null),
            new Formal(Token.NoToken, a.Name, secType, true, false, null),
            new Formal(Token.NoToken, b.Name, secType, true, false, null)
          };
      Expression body = new StmtExpr(Token.NoToken, 
        new AssumeStmt(Token.NoToken, Token.NoToken, assumption, null), 
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, b, new SeqSelectExpr(Token.NoToken, true, l, a, null))
      );

      var orderPredicate = new Predicate(
        Token.NoToken,
        "order",
        false,
        true,
        emptyTypeArgs,
        formals,
        defaultRequires,
        defaultReads,
        defaultEnsures,
        // Create a copy of default decreases, otherwise, during resolution it can be mutated, causing errors during translation.
        // This only happens if there is a name segment using a value from the lattice
        new Specification<Expression>(new List<Expression>(), null),
        body,
        Predicate.BodyOriginKind.OriginalOrInherited,
        null,
        null,
        null,
        null
      );
      // Needed for the type resolution phase
      program.BuiltIns.CreateArrowTypeDecl(formals.Count);
      DefaultClassDecl defaultClass = (DefaultClassDecl)topDecls.Find(x => x.Name == "_default");
      defaultClass.Members.Add(orderPredicate);
    }

    private void DefineLatticeType() {
      if (!topDecls.Exists(x => x.Name == "Lattice")) {
        var module = program.DefaultModuleDef;
        var latticeMap = new MapType(true, secType, new SetType(true, secType));
        var latticeTypeSyn = new TypeSynonymDecl(Token.NoToken, "Lattice", new TypeParameter.TypeParameterCharacteristics(false), emptyTypeArgs, module, latticeMap, null);
        this.latticeType = UserDefinedType.FromTopLevelDecl(Token.NoToken, latticeTypeSyn);
        // Insert after Sec
        topDecls.Insert(1, latticeTypeSyn);
      } else {
        this.latticeType = UserDefinedType.FromTopLevelDecl(Token.NoToken, topDecls.Find(x => x.Name == "Lattice" && x is TypeSynonymDecl));
      }

    }

    private void DefineSec() {
      List<DatatypeCtor> ctors = new List<DatatypeCtor>();
      var members = new List<MemberDecl>();

      var module = program.DefaultModuleDef;
      if (!topDecls.Exists(x => x.Name == "Sec")) {
        // As default, define a binary lattice
        var lowCtr = new DatatypeCtor(Token.NoToken, "Low", new List<Formal>(), null);
        var highCtr = new DatatypeCtor(Token.NoToken, "High", new List<Formal>(), null);
        ctors.Add(lowCtr);
        ctors.Add(highCtr);
        var secIndData = new IndDatatypeDecl(Token.NoToken, "Sec", module, emptyTypeArgs, ctors, members, null, false);
        secType = UserDefinedType.FromTopLevelDecl(Token.NoToken, secIndData);
        // Add to front so it is defined at the top of the file. Use insert so the actual list is mutated
        topDecls.Insert(0, secIndData);
      } else {
        var secDef = topDecls.Find(x => x.Name == "Sec" && x is IndDatatypeDecl);
        this.numSecLevels = ((IndDatatypeDecl)secDef).Ctors.Count;
        secType = UserDefinedType.FromTopLevelDecl(Token.NoToken, secDef);
      }
    }
    private void Visit(Program program, ref InformationFlowState st) {
      // Default module is not in program.Modules, so visit separately.
      // Visit before other modules so lattice type and Sec are defined
      Visit(program.DefaultModuleDef, ref st);
      foreach (var module in program.Modules()) {
        Visit(module, ref st);
      }
    }

    private void Visit(ModuleDefinition moduleDefinition, ref InformationFlowState st) {
      Visit(defaultClass, ref st);
      foreach (var topLevelDeclaration in moduleDefinition.TopLevelDecls) {
        if (topLevelDeclaration.Name == "_default") {
          continue;
        }
        Visit(topLevelDeclaration, ref st);
      }
    }

    private void Visit(TopLevelDecl topLevelDeclaration, ref InformationFlowState st) {
      switch (topLevelDeclaration) {
        case ClassDecl classDeclaration:
          Visit(classDeclaration, ref st);
          break;
        case IndDatatypeDecl indDataTypeDeclaration:
          Visit(indDataTypeDeclaration, ref st);
          break;
        case TypeSynonymDecl typeSynonymDeclaration:
          Visit(typeSynonymDeclaration, ref st);
          break;
        case ModuleDecl moduleDeclaration:
        case DatatypeDecl dataTypeDeclaration:
        case ValuetypeDecl valueTypeDeclaration:
        case OpaqueTypeDecl opaqueTypeDeclaration:
        case NewtypeDecl newTypeDeclaration:
        default:
          reporter.Message(MessageSource.Other, ErrorLevel.Error, topLevelDeclaration.tok, "Unknown TopLevelDecl");
          VisitUnknown(topLevelDeclaration, "Unknown TopLevelDecl");
          break;
      }
    }

    private void Visit(TypeSynonymDecl typeSynDecl, ref InformationFlowState st) {
      if (typeSynDecl.Name == "Lattice") {
        this.latticeType = UserDefinedType.FromTopLevelDecl(Token.NoToken, typeSynDecl);
      }
    }

    private void Visit(IndDatatypeDecl indDataDecl, ref InformationFlowState st) {
      if (indDataDecl.Name == "Sec") {
        this.numSecLevels = indDataDecl.Ctors.Count;
        secType = UserDefinedType.FromTopLevelDecl(Token.NoToken, indDataDecl);
      }
    }

    private Method genRely(Method m, ref InformationFlowState st) {
      List<AttributedExpression> relyConditions = new List<AttributedExpression>();
      foreach (string ifVar in st.Vars.Keys) {
        // Necessary for calls to order predicate
        relyConditions.Add(new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, callGamma(ifVar), nameSeg("lattice"))));
        relyConditions.Add(new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, callPolicy(ifVar), nameSeg("lattice"))));
        // R2: If variable unchanged, security level is unchanged
        relyConditions.Add(new AttributedExpression(
            new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp, 
              new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, new OldExpr(Token.NoToken, nameSeg(ifVar)), nameSeg(ifVar)),
              new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, new OldExpr(Token.NoToken, callGamma(ifVar)), callGamma(ifVar))
            )
          ));
        // R3: Security level is less than or equal to security policy
        relyConditions.Add(new AttributedExpression(callOrder(callGamma(ifVar), callPolicy(ifVar))));
      }
      return new Method(
        Token.NoToken,
        "Rely"+m.Name,
        false,
        false,
        emptyTypeArgs,
        defaultFormals,
        defaultFormals,
        defaultRequires,
        // Modifies this class
        new Specification<FrameExpression>(new List<FrameExpression>() { new FrameExpression(Token.NoToken, new ThisExpr(Token.NoToken), null)}, null),
        // TODO: Rely conditions as ensures
        relyConditions,
        defaultDecreases(),
        null,
        null,
        null
      );
    }

    private TwoStatePredicate genGuarantee(Method m, ref InformationFlowState st) {
      List<AttributedExpression> requires = new List<AttributedExpression>();
      Expression guaranteeConditions;
      Expression prevExpr = new LiteralExpr(Token.NoToken, true);
      Expression currExpr = new LiteralExpr(Token.NoToken, true);
      bool firstItem = true;
      foreach (string varName in st.Global) {
        if (varName.StartsWith("Gamma_")) {
          // Add to requires, not the body
          requires.Add(new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, nameSeg(varName), nameSeg("lattice"))));
          continue;
        }
        var orderCall = callOrder(callGamma(varName), callPolicy(varName));
        if (firstItem) {
          prevExpr = orderCall;
          currExpr = orderCall;
          firstItem = false;
        } else {
          currExpr = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, prevExpr, orderCall);
          prevExpr = currExpr;
        }
      }
      guaranteeConditions = currExpr;

      return new TwoStatePredicate(
          Token.NoToken,
          "Guarantee"+m.Name,
          false,
          //false,
          emptyTypeArgs,
          // TODO: Add input params. Might not be needed, thanks to 2-state predicates
          defaultFormals,
          requires,
          new List<FrameExpression>() { new FrameExpression(Token.NoToken, new ThisExpr(Token.NoToken), null)},
          defaultEnsures,
          defaultDecreases(),
          guaranteeConditions,
          null,
          null
        );
    }

    private void Visit(ClassDecl classDecl, ref InformationFlowState st) {
      st.currentClassMembers = classDecl.Members;
      var originalMembers = new List<MemberDecl>(classDecl.Members);

      foreach (var member in originalMembers) {
        Visit(member, ref st);
      }

      foreach (Function f in st.funcs) {
        Visit(f, ref st);
      }
      // Methods were skipped visiting initially, so that all information needed for reasoning can be obtained first
      foreach (Method m in st.methods) {
        Visit(m, ref st);
        //Define Rely and Guarantee for this method
        if (!st.addAssertions) {
          if (m.Name == "CAS" || m.Name.StartsWith("Rely") || m is Constructor) {
            continue;
          }
          int methodIndex = classDecl.Members.IndexOf(m);
          if (!classDecl.Members.Exists(x => x.Name == "Rely"+m.Name)) {
            classDecl.Members.Insert(methodIndex, genRely(m, ref st));
          }
          if (!classDecl.Members.Exists(x => x.Name == "Guarantee" + m.Name)) {
            classDecl.Members.Insert(methodIndex, genGuarantee(m, ref st));
          }
        }
      }
      // Visited all these methods, so clear list
      st.methods.Clear();
    }

    private void Visit(MemberDecl memberDeclaration, ref InformationFlowState st) {
      // Must explore fields, then functions (security policies) then methods
      // Explore methods after all fields and functions explored, so that information state is complete
      // i.e. All Global and Ctrl variables are identified for use in assertions during methods
      switch (memberDeclaration) {
        case Field field:
          Visit(field, ref st);
          break;
        case Function function:
          //Visit(function, ref st);
          st.funcs.Add(function);
          break;
        case Method method:
          st.methods.Add(method);
          break;
        default:
          VisitUnknown(memberDeclaration, "During visit member.");
          break;
      }
    }

    private void Visit(Function func, ref InformationFlowState st) {
      if (func.Name.StartsWith("L_")) {
        var controlledVar = func.Name[2..];
        if (st.Vars.ContainsKey(controlledVar)) {
          st.Vars.GetValueOrDefault(controlledVar).securityClassification = func;
        }
        var controlVars = new HashSet<string>();

        // Populate Ctrl and ctrled sets
        getControlVars(func.Body, controlVars, ref st);
        foreach (string ctrlVar in controlVars) {
          HashSet<string> ctrld;
          if (st.Ctrl.TryGetValue(ctrlVar, out ctrld)) {
            ctrld.Add(controlledVar);
          } else {
            ctrld = new HashSet<string>() { controlledVar };
            st.Ctrl.Add(ctrlVar, ctrld);
          }
        }

        // If a security classification has variables in it, but no inputs, redefine with inputs.
        // This is used for substituion in assertions later. Variables are renamed by appending "_in"
        // e.g. varName -> varName_in
        if (st.addAssertions) {
          if (func.Formals.Count == 0 && controlVars.Count != 0) {
            foreach (string variable in controlVars) {
              func.Formals.Add(new Formal(Token.NoToken, variable + "_in", st.Vars.GetValueOrDefault(variable).varType, true, false, nameSeg(variable)));
            }
            func.Body = renameFuncBody(func.Body, controlVars, ref st);
            program.BuiltIns.CreateArrowTypeDecl(controlVars.Count);
          }
        }
        
      }
    }

    // Renames namesegments in a given expression from "name" to "name_in". Used when adding paramters to a security classification
    // For the use case of information flow, these are if then else expressions.
    private Expression renameFuncBody(Expression expr, HashSet<string> ctrlVars, ref InformationFlowState st) {
      switch (expr) {
        case ITEExpr iteeExpr:
          var newTest = renameFuncBody(iteeExpr.Test, ctrlVars, ref st);
          var newThen = renameFuncBody(iteeExpr.Thn, ctrlVars, ref st);
          var newElse = renameFuncBody(iteeExpr.Els, ctrlVars, ref st);
          return new ITEExpr(iteeExpr.tok, iteeExpr.IsBindingGuard, newTest, newThen, newElse);
        case BinaryExpr binExpr:
          var newE0 = renameFuncBody(binExpr.E0, ctrlVars, ref st);
          var newE1 = renameFuncBody(binExpr.E1, ctrlVars, ref st);
          return new BinaryExpr(Token.NoToken, binExpr.Op, newE0, newE1);
        case NameSegment nameSegment:
          if (st.Global.Contains(nameSegment.Name)) {
            return nameSeg(nameSegment.Name + "_in", nameSegment.OptTypeArguments);
          } else {
            return nameSegment;
          }
        case LiteralExpr:
          // Literal Expressions are not variables, so continue
          return expr;
        case ParensExpression pEpxr:
          var newParens = renameFuncBody(pEpxr.E, ctrlVars, ref st);
          return new ParensExpression(pEpxr.tok, newParens);
        default:
          VisitUnknown(expr, "Rename Func Body function");
          return null;
      }
    }

    private void getControlVars(Expression expr, HashSet<string> ctrlVars, ref InformationFlowState st) {
      switch (expr) {
        case ITEExpr iteeExpr:
          getControlVars(iteeExpr.Test, ctrlVars, ref st);
          getControlVars(iteeExpr.Thn, ctrlVars, ref st);
          getControlVars(iteeExpr.Els, ctrlVars, ref st);
          break;
        case BinaryExpr binExpr:
          getControlVars(binExpr.E0, ctrlVars, ref st);
          getControlVars(binExpr.E1, ctrlVars, ref st);
          break;
        case NameSegment nameSeg:
          //if (nameSeg.Name.EndsWith("_in")) {
            //var name = nameSeg.Name.Substring(0, nameSeg.Name.Length - 3);
            //if (st.Global.Contains(name)) {
            //  ctrlVars.Add(name);
            //}
          //}
          if (st.Global.Contains(nameSeg.Name)) {
            ctrlVars.Add(nameSeg.Name);
          }
          break;
        case LiteralExpr:
          // Literal Expressions are not variables, so continue
          break;
        case ParensExpression pExpr:
          getControlVars(pExpr.E, ctrlVars, ref st);
          break;
        default:
          VisitUnknown(expr, "During getControlVars.");
          break;
      }
    }

    // Returns true if valid, else returns false
    private bool validateLattice(Field field) {
      bool result = false;
      if (field is ConstantField constField) {
        var rhs = (MapDisplayExpr)constField.Rhs;
        var highestCount = 0;
        var lowestCount = 100;
        if (rhs.Elements.Count != numSecLevels) {
          reporter.Error(MessageSource.Other, field.tok, $"Lattice definition contains the wrong number Sec values. Check all Sec values are mapped exactly once.");
          return result;
        }
        foreach (ExpressionPair item in rhs.Elements) {
          if (item.B is SetDisplayExpr setExpr) {
            var numEls = setExpr.Elements.Count;
            if (numEls > highestCount) {
              highestCount = numEls;
              lowestSec = item.A;
            }
            if (numEls < lowestCount) {
              lowestCount = numEls;
              highestSec = item.A;
            }
            result = true;
          } else {
            // Not a valid definition for a lattice.
            VisitUnknown(item.B, "Lattice Definition Error");
            return false;
          }
        }
        if (lowestCount != 1) {
          reporter.Error(MessageSource.Other, field.tok, $"Lattice definition does not contain a highest element. The highest element had {lowestCount} higher elements instead of 1.");
          result = false;
        }
        if (highestCount != numSecLevels) {
          reporter.Error(MessageSource.Other, field.tok, $"Lattice definition does not contain a lowest element. The lowest element had {highestCount} higher elements instead of {numSecLevels}.");
          result = false;
        }
      } else {
        reporter.Warning(MessageSource.Other, field.tok, "Define the lattice as a constant field");
        result = false;
      }
      return result;
    }

    private Function generateSecurityPolicy(Field field) {
      program.BuiltIns.CreateArrowTypeDecl(defaultFormals.Count);

      return new Function(
        Token.NoToken, 
        "L_" + field.Name, 
        false, 
        false, // Non-ghost makes it a function method, which is needed if it is called in non-specification contexts, like a parameter to a method
        emptyTypeArgs, 
        defaultFormals, 
        null, 
        secType,
        defaultRequires, 
        defaultReads, 
        defaultEnsures,
        defaultDecreases(),
        nameSeg("FILL_THIS_IN"),
        null, 
        null, 
        null, 
        null
      );
    }

    private void Visit(Field field, ref InformationFlowState st) {
      if (field.Name == "Repr") {
        return;
      }
      if (field is ConstantField constField) {
        if (constField.Name == "secAttack" || constField.Name == "joinMap" || constField.Name == "meetMap") {
          // Don't add security levels or policies for these boilerplate vars
          return;
        }
        // To allow the user to name the variable what they want, compare the type
        // Directly comparing the types doesn't work yet, as they have not been resolved
        if (constField.Type.ToString() == latticeType.ToString()) {
          // Check the lattice has a highest and lowest value, and contains a mapping for all Sec types
          // I.e. one set maps to a single value, and one maps to all values in the Sec datatype
          if (st.addAssertions) {
            if (validateLattice(field)) {
              latticeDef = constField;
              if (latticeDef.Rhs is MapDisplayExpr mapExpr) {
                userLattice = new Lattice();
                foreach (ExpressionPair exprP in mapExpr.Elements) {
                  var key = ((NameSegment)exprP.A).Name;
                  var values = ((SetDisplayExpr)exprP.B).Elements;
                  var highSet = new HashSet<string>();
                  foreach (NameSegment name in values) {
                    highSet.Add(name.Name);
                  }
                  userLattice.AddHighMap(key, highSet);
                }
                defineJoin();
                defineMeet();
              } else {
                reporter.Error(MessageSource.Other, field.tok, "Error validating the lattice. There is an error in the map definition.");
              }
            }
          }
          // Don't make gamma or security classification for the lattice
          return;
        }
      }

      var fieldIndex = st.currentClassMembers.IndexOf(field);
      
      if (!field.Name.StartsWith("Gamma_")) {
        if (st.Vars.ContainsKey(field.Name)) {
          var infoVar = st.Vars.GetValueOrDefault(field.Name);
          infoVar.Variable = field;
        } else {
          st.Vars.Add(field.Name, new InformationFlowVar(field));
        }

        if (!st.currentClassMembers.Exists(x => x.Name == "Gamma_" + field.Name)) {
          var gammaField = new Field(Token.NoToken, "Gamma_" + field.Name, false, secType, null);
          st.currentClassMembers.Insert(fieldIndex, gammaField);
          st.Global.Add("Gamma_" + field.Name);
          //st.Vars.GetValueOrDefault(field.Name).securityLevel = gammaField;
        }


        if (!st.currentClassMembers.Exists(x => x.Name == "L_" + field.Name)) {
          var securityClassification = generateSecurityPolicy(field);
          st.currentClassMembers.Insert(fieldIndex, securityClassification);
          st.Vars.GetValueOrDefault(field.Name).securityClassification = securityClassification;
        }
      } else {
        // Name without gamma prefix
        var varName = field.Name[6..];
        //reporter.Warning(MessageSource.Other, field.tok, "A Gamma variable exists for a non-existent field " + varName);
        if (st.Vars.ContainsKey(varName)) {
          st.Vars.GetValueOrDefault(varName).securityLevel = field;
        } else {
          var infoVar = new InformationFlowVar(varName) {
            securityLevel = field
          };
          st.Vars.Add(varName, infoVar);
        }
      }

      st.Global.Add(field.Name);
    }

    private DatatypeValue createTwoTuple(Expression pos0, Expression pos1) {
      return new DatatypeValue(Token.NoToken, "_tuple#2", BuiltIns.TupleTypeCtorNamePrefix + 2,
            new List<ActualBinding>() {
              new ActualBinding(null, pos0),
              new ActualBinding(null, pos1)
            });
    }

    private void defineMeet() {
      // Define a map for meet, and a function to call so that Dafny can assume inputs are in the lattice
      // MEET MAP 
      var secTwoTuple = new UserDefinedType(Token.NoToken, "_tuple#2", new List<Microsoft.Dafny.Type>() { secType, secType });
      Microsoft.Dafny.Type meetMapType = new MapType(true, secTwoTuple, secType);
      //var map = (MapDisplayExpr)latticeDef.Rhs;
      List<ExpressionPair> elements = new List<ExpressionPair>();
      // for each sec value in the lattice:
      //  // Expression pair is Sec --> set<Sec>
      foreach (string sec in userLattice.lowMap.Keys) {
        foreach (string sec2 in userLattice.lowMap.Keys) {
          // Always a 2-tuple
          var keyTuple = createTwoTuple(nameSeg(sec), nameSeg(sec2));
          var intersection = new HashSet<string>(userLattice.lowMap.GetValueOrDefault(sec));
          intersection.IntersectWith(userLattice.lowMap.GetValueOrDefault(sec2));
          var joinVal = nameSeg(userLattice.invLowMap.GetValueOrDefault(intersection, "ERROR"));
          elements.Add(new ExpressionPair(keyTuple, joinVal));
        }
      }
      var meetMap = new MapDisplayExpr(Token.NoToken, true, elements);
      defaultClass.Members.Add(new ConstantField(Token.NoToken, "meetMap", meetMap, false, false, meetMapType, null));
      // END MEET MAP
      // MEET FUNCTION
      var a = nameSeg("a");
      var b = nameSeg("b");
      List<Formal> formals = new List<Formal>() {
            new Formal(Token.NoToken, a.Name, secType, true, false, null),
            new Formal(Token.NoToken, b.Name, secType, true, false, null)
          };
      var assumption = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And,
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, a, nameSeg("lattice")),
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, b, nameSeg("lattice"))
      );
      Expression body = new StmtExpr(Token.NoToken,
        new AssumeStmt(Token.NoToken, Token.NoToken, assumption, null),
        new SeqSelectExpr(Token.NoToken, true, nameSeg("meetMap"),
          new DatatypeValue(Token.NoToken, "_tuple#2", BuiltIns.TupleTypeCtorNamePrefix + 2,
            new List<ActualBinding>() {
              new ActualBinding(null, a),
              new ActualBinding(null, b)
            }),
          null
        )
      );
      var meet = new Function(
        Token.NoToken,
        "meet",
        false,
        false, // Non-ghost makes it a function method, which is needed if it is called in non-specification contexts, like a parameter to a method
        emptyTypeArgs,
        formals,
        null,
        secType,
        defaultRequires,
        defaultReads,
        defaultEnsures,
        defaultDecreases(),
        body,
        null,
        null,
        null,
        null
      );
      defaultClass.Members.Add(meet);
      // Needed for the type resolution phase
      program.BuiltIns.CreateArrowTypeDecl(formals.Count);
      // END MEET FUNCTION
    }

    private void defineJoin() {
      // Define a map for join, and a function to call so that Dafny can assuem inputs are in the lattice
      // JOIN MAP
      var secTwoTuple = new UserDefinedType(Token.NoToken, "_tuple#2", new List<Microsoft.Dafny.Type>() { secType, secType });
      Microsoft.Dafny.Type joinMapType = new MapType(true, secTwoTuple, secType);
      List<ExpressionPair> elements = new List<ExpressionPair>();
      foreach (string sec in userLattice.highMap.Keys) {
        foreach (string sec2 in userLattice.highMap.Keys) {
          // Always a 2-tuple
          var keyTuple = new DatatypeValue(Token.NoToken, "_tuple#2", BuiltIns.TupleTypeCtorNamePrefix + 2, 
            new List<ActualBinding>() { 
              new ActualBinding(null, nameSeg(sec)),
              new ActualBinding(null, nameSeg(sec2))
            });
          var intersection = new HashSet<string>(userLattice.highMap.GetValueOrDefault(sec));
          intersection.IntersectWith(userLattice.highMap.GetValueOrDefault(sec2));
          var joinVal = nameSeg(userLattice.invHighMap.GetValueOrDefault(intersection, "ERROR"));
          elements.Add(new ExpressionPair(keyTuple, joinVal));
        }
      }
      var joinMap = new MapDisplayExpr(Token.NoToken, true, elements);
      defaultClass.Members.Add(new ConstantField(Token.NoToken, "joinMap", joinMap, false, false, joinMapType, null));
      // END JOIN MAP
      // JOIN FUNCTION
      var a = nameSeg("a");
      var b = nameSeg("b");
      List<Formal> formals = new List<Formal>() {
            new Formal(Token.NoToken, a.Name, secType, true, false, null),
            new Formal(Token.NoToken, b.Name, secType, true, false, null)
          };
      var assumption = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And,
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, a, nameSeg("lattice")),
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, b, nameSeg("lattice"))
      );
      Expression body = new StmtExpr(Token.NoToken,
        new AssumeStmt(Token.NoToken, Token.NoToken, assumption, null),
        new SeqSelectExpr(Token.NoToken, true, nameSeg("joinMap"), 
          new DatatypeValue(Token.NoToken, "_tuple#2", BuiltIns.TupleTypeCtorNamePrefix + 2,
            new List<ActualBinding>() {
              new ActualBinding(null, a),
              new ActualBinding(null, b)
            }), 
          null
        )
      );
      var join = new Function(
        Token.NoToken,
        "join",
        false,
        false, // Non-ghost makes it a function method, which is needed if it is called in non-specification contexts, like a parameter to a method
        emptyTypeArgs,
        formals,
        null,
        secType,
        defaultRequires,
        defaultReads,
        defaultEnsures,
        defaultDecreases(),
        body,
        null,
        null,
        null,
        null
      );
      // Needed for the type resolution phase
      program.BuiltIns.CreateArrowTypeDecl(formals.Count);
      defaultClass.Members.Add(join);
      //END JOIN FUNCTION
    }

    private UpdateStmt defaultGamma(string name) {
      string varName = name.StartsWith("Gamma_") ? name : "Gamma_" + name;
      var lhs = new List<Expression>() { nameSeg(varName)};
      var rhs = new List<AssignmentRhs>() { new ExprRhs(highestSec) };
      return new UpdateStmt(Token.NoToken, Token.NoToken, lhs, rhs);
    }

    private void Visit(Method method, ref InformationFlowState st) {
      if (method.Name == "CAS" || method.Name.StartsWith("Rely") || method is Constructor) {
        return;
      }
      st.parentMethod = method;
      // Add modifies this if not added
      // Needed for assertions since Rely Calls modifies this, and the body of the method cannot modify something not in the parent modifies clause
      if (st.addAssertions) {
        if (!method.Mod.Expressions.Exists(x => x.E is ThisExpr)) {
          method.Mod.Expressions.Add(new FrameExpression(Token.NoToken, new ThisExpr(Token.NoToken), null));
        }
      }
      if (method.Body != null) {
        var paramGamas = new List<UpdateStmt>();
        if (method.Outs.Count != 0) {
          // Return statements are treated as assignments to globals, so generate required information flow variables
          foreach (Formal outVar in method.Outs) {
            var varName = method.Name + "_return_" + outVar.Name;
            if (!st.currentClassMembers.Exists(x=>x.Name == varName)) {
              var newGlobal = new Field(Token.NoToken, varName, false, outVar.Type, null);
              var newGlobalGamma = new Field(Token.NoToken, "Gamma_" + method.Name + "_return_" + outVar.Name, false, secType, null);
              st.Vars.Add(varName, new InformationFlowVar(newGlobal) { securityLevel = newGlobalGamma });
              st.currentClassMembers.Insert(0, newGlobal);
              st.currentClassMembers.Insert(1, newGlobalGamma);
            }
            if (st.addAssertions) {
              // Initialise gamma for inputs to highestSec at the start of the method
              // These will be added to the body of the method at the end of visiting all children
              paramGamas.Add(defaultGamma(varName));
            }
            if (!st.currentClassMembers.Exists(x => x.Name == "L_" + varName)) {
              Field varField;
              if (st.Vars.TryGetValue(varName, out InformationFlowVar mainVar)) {
                varField = mainVar.Variable;
              } else {
                varField = new Field(Token.NoToken, varName, false, outVar.Type, null);
              }
              var securePolicy = generateSecurityPolicy(varField);
              st.currentClassMembers.Insert(2, securePolicy);
            }
          }
        }

        if (method.Ins.Count > 0) {
          foreach (Formal inVar in method.Ins) {
            var varName = method.Name + "_In_" + inVar.Name;
            if (!st.currentClassMembers.Exists(x => x.Name == varName)) {
              var newGlobal = new Field(Token.NoToken, varName, false, inVar.Type, null);
              var newGlobalGamma = new Field(Token.NoToken, "Gamma_" + method.Name + "_In_" + inVar.Name, false, secType, null);
              st.Vars.Add(varName, new InformationFlowVar(newGlobal) { securityLevel = newGlobalGamma });
              st.currentClassMembers.Insert(0, newGlobal);
              st.currentClassMembers.Insert(1, newGlobalGamma);
            }
            // Initialise gamma for inputs to highestSec at the start of the method
            if (st.addAssertions) {
              // These will be added to the body of the method at the end of visiting all children
              paramGamas.Add(defaultGamma(varName));
            }
            if (!st.currentClassMembers.Exists(x => x.Name == "L_" + varName)) {
              Field varField;
              if (st.Vars.TryGetValue(varName, out InformationFlowVar mainVar)) {
                varField = mainVar.Variable;
              } else {
                varField = new Field(Token.NoToken, varName, false, inVar.Type, null);
              }
              var securePolicy = generateSecurityPolicy(varField);
              st.currentClassMembers.Insert(2, securePolicy);
            }
          }
        }
        // If there is a call to another method, the labelNum will be reset, so store it before visiting body
        var currentLabel = st.labelNum;
        Visit(method.Body, ref st);
        st.localVars.Clear();
        st.labelNum = currentLabel;

        if (st.addAssertions) {
          // Add Gammas for in and out params after all other assertions so they are not labelled and do not have rely Guarantee calls.
          // This is ok since this is just initialising the value to the highest security value, so that Dafny can reason about them.
          foreach(UpdateStmt updGamma in paramGamas) {
            method.Body.Body.Insert(0, updGamma);
          }
        }
      }
      st.parentMethod = null;
    }

    private void Visit(BlockStmt block, ref InformationFlowState st) {
      // Copy the list so we don't mutate during iteration
      var loopBody = new List<Statement>(block.Body);
      var currentParentStmtList = st.parentStmtList;
      st.parentStmtList = block.Body;
      var oldPrevCas = st.prevCAS;
      // Start of a new scope
      st.prevCAS = false;
      
      foreach (Statement stmt in loopBody) {
        Visit(stmt, ref st);
      }

      st.parentStmtList = currentParentStmtList;
      st.prevCAS = oldPrevCas;
      // Exiting block scope, clear local vars
      // This has issues for blocks such as if statments, since local vars is meant to track local to the method. Clear at end of method

      //st.localVars.Clear();
      //block.Body = infoFlowBody;
    }

    private void Visit(Statement stmt, ref InformationFlowState st) {
      AssertStmt assertion;
      int stmtIndex = st.parentStmtList.IndexOf(stmt);
      switch (stmt) {
        case UpdateStmt updateStmt:
          Visit(updateStmt, ref st);
          if (st.addAssertions) {
            assertion = genInfoFlowAssertionAssignment(updateStmt, ref st);
            if (assertion is not null) {
              //stmtIndex = st.parentStmtList.IndexOf(stmt);
              if (stmtIndex == -1) {
                // Can't find update statment. In a new block scope, so insert at start
                reporter.Warning(MessageSource.Other, stmt.Tok, "Can't find update statement for " + stmt.ToString());
              } else {
                st.parentStmtList.Insert(stmtIndex, assertion);
              }
            }
          } 
          break;
        // Assign Statement is never created by the parser. Update statement is used for assignment
        //case AssignStmt assignStmt:
        //  addInfoFlowAssertionAssignment(assignStmt, ref st);
        //  break;
        case VarDeclStmt varStmt:
          
          if (st.addAssertions) {
            var startLocals = new List<LocalVariable>(varStmt.Locals);
            foreach (LocalVariable local in startLocals) {
              if (startLocals.Exists(x => x.Name.StartsWith("Gamma_"))) {
                // Don't add a gamma if it is already there
                continue;
              }
              //varStmt.Locals.Add(new LocalVariable(Token.NoToken, Token.NoToken, "Gamma_" + local.Name, secType, false));
              var level = new VarDeclStmt(Token.NoToken, Token.NoToken, new List<LocalVariable>() {
                new LocalVariable(Token.NoToken, Token.NoToken, "Gamma_" + local.Name, secType, false)
              }, null);
              st.parentStmtList.Insert(stmtIndex, level);
            }
            assertion = genInfoFlowAssertionAssignment(varStmt, ref st);
            if (assertion is not null) {
              //stmtIndex = st.parentStmtList.IndexOf(stmt);
              st.parentStmtList.Insert(stmtIndex, assertion);
            }
          } else {
            if (varStmt.Update is not null) {
              Visit(varStmt.Update, ref st);
              // Add Default value to RHS
            }
          }
          break;
        case IfStmt ifStmt:
          // Gen assertion for the guard
          if (st.addAssertions) {
            // Assert level of guard is less than secattack
            var guardCheck = new AssertStmt(Token.NoToken, Token.NoToken, callOrder(calcGammaE(ifStmt.Guard, ref st), nameSeg("secAttack")), null, null, null);
            st.parentStmtList.Insert(stmtIndex, guardCheck);
          }
          Visit(ifStmt.Thn, ref st);
          if (ifStmt.Els is not null) {
            Visit(ifStmt.Els, ref st);
            // Don't label else branch
            ifStmt.Els.Labels = null;
          }
          st.prevCAS = false;
          break;
        case BlockStmt bStmt:
          Visit(bStmt, ref st);
          st.prevCAS = false;
          break;
        case ReturnStmt rStmt:
          if (st.addAssertions) {
            var j = 0;
            foreach (var rhs in rStmt.rhss) {
              var globalReturn = st.parentMethod.Name + "_return_" + st.parentMethod.Outs[j].Name;
              // Like assignment to global
              var globalUpdate = new UpdateStmt(Token.NoToken, Token.NoToken,
                new List<Expression>() { nameSeg(globalReturn) },
                new List<AssignmentRhs>() { rhs }
               );
              var returnAssertion = genInfoFlowAssertionAssignment(globalUpdate, ref st);
              st.parentStmtList.Insert(st.parentStmtList.IndexOf(rStmt), returnAssertion);
              j++;
            }
          }
          //rStmt.hiddenUpdate
          st.prevCAS = false;
          break;
        case WhileStmt wStmt:
          // Add assertion for guards
          if (st.addAssertions) {
            // Termination not needed to be proved for info flow, so add decreases * to loop and method
            var parentDecreases = st.parentMethod.Decreases;
            if (!parentDecreases.Expressions.Exists(x => x.tok.val == "*")) {
              parentDecreases.Expressions.Add(new WildcardExpr(Token.NoToken));
            }

            var newDecreases = new Specification<Expression>(new List<Expression>() { new WildcardExpr(Token.NoToken) }, null);
            var newWhile = new WhileStmt(wStmt.Tok, wStmt.EndTok, wStmt.Guard, wStmt.Invariants, newDecreases, wStmt.Mod, wStmt.Body) {
              Labels = wStmt.Labels
            };
            stmt = newWhile;
            st.parentStmtList.Insert(stmtIndex, newWhile);
            st.parentStmtList.RemoveAt(stmtIndex + 1);
            
            // Assert level of guard is less than secattack
            var guardCheck = callOrder(calcGammaE(wStmt.Guard, ref st), nameSeg("secAttack"));
            Expression invariants;
            if (wStmt.Invariants.Count == 0) {
              invariants = new LiteralExpr(Token.NoToken, true);
            } else
            if (wStmt.Invariants.Count == 1) {
              invariants = wStmt.Invariants[0].E;
            } else {
              var prevExpr = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, wStmt.Invariants[0].E, wStmt.Invariants[1].E);
              BinaryExpr currExpr = prevExpr;
              for (var i=2; i < wStmt.Invariants.Count; i++) {
                currExpr = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, prevExpr, wStmt.Invariants[i].E);
                prevExpr = currExpr;
              }
              invariants = currExpr;
            }
            var whileAssertion = new AssertStmt(Token.NoToken, Token.NoToken, new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp, invariants, guardCheck), null, null, null);
            st.parentStmtList.Insert(stmtIndex, whileAssertion);

            // If the while guard is based on a CAS (prev statment was a CAS) then add invariants so dafny can prove it
            // Add after other assertions, so only user provided invariants are used to verify information flow
            if (st.prevCAS) {
              wStmt.Invariants.Add(new AttributedExpression(st.casInvariant));
            }
          }
          Visit(wStmt.Body, ref st);
          st.prevCAS = false;
          break;
        default:
          VisitUnknown(stmt, "During statement visit.");
          st.prevCAS = false;
          break;
      }

      if (st.addAssertions) {
        // Update stmtIndex since assertions have been added
        //stmtIndex = st.parentStmtList.IndexOf(stmt);
        var labelName = "" + st.labelNum++;
        stmt.Labels = new LList<Label>(new Label(Token.NoToken, labelName), stmt.Labels);
        if (stmt is not BlockStmt) {
          st.parentStmtList.Insert(stmtIndex, new UpdateStmt(Token.NoToken, Token.NoToken,
          new List<Expression>(), new List<AssignmentRhs>() { new ExprRhs(callRely(st.parentMethod.Name)) }));
          var guarCall = new AssertStmt(Token.NoToken, Token.NoToken, callGuar(st.parentMethod.Name, new Token() { val = labelName }), null, null, null);
          if (stmt is WhileStmt wStmt) {
            var guaranteeMethod = callGuar(st.parentMethod.Name, new Token() { val = labelName });
            wStmt.Invariants.Add(new AttributedExpression(guaranteeMethod));
            foreach (string varName in st.Global) {
              if (varName.StartsWith("Gamma_")) {
                // Don't add input or output gamma vars
                if (varName.Contains("_return_") || varName.Contains("_In_")) {
                  continue;
                }
                // invariants before guarantee call
                wStmt.Invariants.Insert(0, new AttributedExpression(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, nameSeg(varName), nameSeg("lattice"))));
                
              }
            }
          }
          if (st.parentStmtList.IndexOf(stmt) + 1 < st.parentStmtList.Count) {
            st.parentStmtList.Insert(st.parentStmtList.IndexOf(stmt) + 1, guarCall);
          } else {
            st.parentStmtList.Add(guarCall);
          }
          
        }
      }
    }

    private void Visit(UpdateStmt updStmt, ref InformationFlowState st) {
      if (updStmt.Lhss.Count == 1) {
        if (st.addAssertions) {
          string name = getExprName(updStmt.Lhss[0]);
          if (name.StartsWith("Gamma_")) {
            return;
          }
          if (st.parentMethod.Outs.Exists(x => x.Name == name)) {
            name = st.parentMethod.Name + "_return_" + name;
          }

          var infoVar = st.Vars.GetValueOrDefault(name, null);
          if (infoVar is not null) {
            updStmt.Lhss.Add(nameSeg("Gamma_" + name));
          } else {
            updStmt.Lhss.Add(new IdentifierExpr(Token.NoToken, "Gamma_" + name));
          }
          Expression rhsExpr;
          switch (updStmt.Rhss[0]) {
            case ExprRhs eRhs:
              rhsExpr = eRhs.Expr;
              break;
            //case TypeRhs tRhs:
            //case HavocRhs hRhs:
            //  break;
            default:
              VisitUnknown(updStmt.Rhss[0], "Unknown/unimplemented assignment rhs");
              rhsExpr = nameSeg("Unknown");
              break;
          }
          updStmt.Rhss.Add(new ExprRhs(calcGammaE(rhsExpr, ref st)));
        }
      } else {
        if (updStmt.Rhss.Count == 1) {
          var expr = getRhsExpr(updStmt.Rhss[0]);
          if (expr is ApplySuffix methodCall) {
            if (methodCall.Lhs is NameSegment methodName && methodName.Name == "CAS") {
              st.prevCAS = true;
              if (st.addAssertions) {
                // Add Gamma for bool and input value

                // Define RHS for CAS vars here
                // Add assertion for CAS check
                var casGuard = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, methodCall.Bindings.ArgumentBindings[0].Actual, methodCall.Bindings.ArgumentBindings[1].Actual);
                AssertStmt casAssert = new AssertStmt(Token.NoToken, Token.NoToken, 
                  new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp, casGuard, callOrder(calcGammaE(casGuard, ref st), nameSeg("secAttack")))
                  , null, null, null);
                st.parentStmtList.Insert(st.parentStmtList.IndexOf(updStmt), casAssert);


                string outName = getExprName(updStmt.Lhss[1]);
                string boolName = getExprName(updStmt.Lhss[0]);
                st.casInvariant = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp,
                  nameSeg(boolName),
                  new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, methodCall.Bindings.ArgumentBindings[0].Actual, methodCall.Bindings.ArgumentBindings[2].Actual)
                );
                var gammaLHS = new List<Expression>();
                foreach (Expression lhsExpr in updStmt.Lhss) {
                  gammaLHS.Add(nameSeg("Gamma_" + getExprName(lhsExpr)));
                }
                var gammaRHS = new List<AssignmentRhs>();
                //First output of CAS is a bool, and has security level dependent on the CAS guard
                gammaRHS.Add(new ExprRhs(calcGammaE(casGuard, ref st)));
                var outVarGamma = new ITEExpr(Token.NoToken, false, casGuard, calcGammaE(methodCall.Bindings.ArgumentBindings[1].Actual, ref st), callGamma(outName));
                gammaRHS.Add(new ExprRhs(outVarGamma));
                //gammaRHS.Add(new ExprRhs(calcGammaE(casGuard, ref st)));

                var gammaCas = new UpdateStmt(Token.NoToken, Token.NoToken, gammaLHS, gammaRHS);
                if (st.parentStmtList.IndexOf(updStmt) + 1 > st.parentStmtList.Count) {
                  st.parentStmtList.Add(gammaCas);
                } else {
                  st.parentStmtList.Insert(st.parentStmtList.IndexOf(updStmt) + 1, gammaCas);
                }
              }
            } else {
              st.prevCAS = false;
            }
          } else {
            //var expr = getRhsExpr(updStmt.Rhss[0]);
          }
        }
      }
    }

    private AssertStmt genInfoFlowAssertionAssignment(VarDeclStmt varStmt, ref InformationFlowState st) {
      foreach (LocalVariable local in varStmt.Locals) {
        st.localVars.Add(local.Name);
      }

      if (varStmt.Update is not null) {
        var stmt = (UpdateStmt)varStmt.Update;

        return genInfoFlowAssertionAssignment(stmt, ref st);
      } else {
        return null;
      }
    }

    private Expression getRhsExpr(AssignmentRhs rhs) {
      switch (rhs) {
        case ExprRhs eRhs:
          return eRhs.Expr;
        //case TypeRhs tRhs:
          //tRhs
        //case HavocRhs hRhs:
        //  break;
        default:
          VisitUnknown(rhs, "Unknown/unimplemented assignment rhs");
          return nameSeg("UNKNOWN_RHS");
      }
    }

    private string getExprName(Expression e) {
      switch (e) {
        case NameSegment nameSeg:
          return nameSeg.Name;
        case AutoGhostIdentifierExpr idExpr:
          return idExpr.Name;
        default:
          VisitUnknown(e, "Unknown LHS while generating assertions. Given expression does not have a name");
          return "UNKNOWN";
      }
    }

    private AssertStmt genInfoFlowAssertionAssignment(UpdateStmt stmt, ref InformationFlowState st) {
      AssertStmt assertion = new AssertStmt(Token.NoToken, null, new LiteralExpr(Token.NoToken, true), null, null, null);
      if (stmt.Rhss.Count != stmt.Lhss.Count) {
        if (stmt.Rhss.Count == 1 && ((ExprRhs)stmt.Rhss[0]).Expr is ApplySuffix) {
          //TODO: If CAS statement, handle differently
          // Add gamma for each afterwards, based off cas inputs.
          // Set flag stating CAS call made, so while statements can be modified.
          return null;
        } else {
          reporter.Error(MessageSource.Other, stmt.Tok, "LHS of assignment does not match RHS. Check Gamma_ variable is assigned a value.");
          return null;
        }
      }

      // Since every variable should have a gamma defined, there should be an even number of variables
      //if (stmt.Lhss.Count % 2 != 0) {
      //  reporter.Error(MessageSource.Other, stmt.Tok, "Error in Information Flow Injector: A Gamma Variable appears to be missing.");
      //}

      // TODO: Handle multiple assignment?
      // Assumed structure (true by construction) is that directly after each variable in a multiple assingment, is its gamma variable
      //for (var i = 0; i < stmt.Lhss.Count; i++) {
      var lhs = stmt.Lhss[0];//[i];
      //var gammaLhs = stmt.Lhss[1];
      var rhs = stmt.Rhss[0];//[i];
      if (stmt.Rhss.Count > 1) {
        var gammaRhs = stmt.Rhss[1];
        Expression gammaRhsExpr = getRhsExpr(gammaRhs); ;
      }
     
      Expression rhsExpr = getRhsExpr(rhs); ;
      

      string name = getExprName(lhs);
      
      if (name.StartsWith("Gamma_")) {
        // Don't add assertions for updating the defaultGamma of inputs
        return null;
      }

      var isLocalVar = st.localVars.Contains(name);
      if (isLocalVar) {
        // Local variables do not leak information, so they always assert true
        return assertion;
      } else {
      // Since the variable is global, it must have a policy already defined
      if (st.parentMethod.Outs.Exists(x =>x.Name == name)) {
        name = st.parentMethod.Name + "_return_" + name;
      }
      var globalImplication = callOrder(calcGammaE(rhsExpr, ref st), callPolicy(name));

        Expression secureUpd = null;
        if (st.Ctrl.ContainsKey(name)) {
          var ctrled = st.Ctrl.GetValueOrDefault(name, new HashSet<string>());
          ApplySuffix meet;
          ApplySuffix LSubstitution;
          ApplySuffix currSecureUpd;

        foreach (string variable in ctrled) {   
          meet = meetCall(callGamma(variable), callPolicy(variable));
            // L(ctrled)[x<-e]
            var lSubBinding = new List<ActualBinding>();
            if (st.Vars.GetValueOrDefault(variable).securityClassification.Formals.Count >= 1) {
              lSubBinding.Add(new ActualBinding(null, rhsExpr));
            }
            LSubstitution = new ApplySuffix(
              Token.NoToken,
              null,
              nameSeg("L_" + variable),
              lSubBinding
            );
            currSecureUpd = callOrder(meet, LSubstitution);

            if (secureUpd is null) {
              secureUpd = currSecureUpd;
            } else {
              secureUpd = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, currSecureUpd, secureUpd);
            }

          }
          var fullAssertion = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, globalImplication, secureUpd);
          assertion = new AssertStmt(Token.NoToken, Token.NoToken, fullAssertion, null, null, null);

        } else {
          assertion = new AssertStmt(Token.NoToken, Token.NoToken, globalImplication, null, null, null);
        }
      }
      return assertion;
    }

    private void VisitUnknown(object node, string customError) {
      reporter.Warning(MessageSource.Other, Token.NoToken, "Unknown node of type " + node.GetType().Name + ". " + customError);
    }

    private ApplySuffix joinCall(Expression sec1, Expression sec2) {
      //return new SeqSelectExpr(Token.NoToken, true, nameSeg("join"), createTwoTuple(sec1, sec2), null);
      return new ApplySuffix(Token.NoToken, null, nameSeg("join"), new List<ActualBinding> { new ActualBinding(null, sec1), new ActualBinding(null, sec2) });
    }

    private ApplySuffix meetCall(Expression sec1, Expression sec2) {
      //return new SeqSelectExpr(Token.NoToken, true, nameSeg("meet"), createTwoTuple(sec1, sec2), null);
      return new ApplySuffix(Token.NoToken, null, nameSeg("meet"), new List<ActualBinding> { new ActualBinding(null, sec1), new ActualBinding(null, sec2) });
    }

    private ApplySuffix callRely(string methodName) {
      return new ApplySuffix(
                 Token.NoToken,
                 null,
                 nameSeg("Rely" + methodName),
                 new List<ActualBinding>()
               );
    }

    private ApplySuffix callGuar(string methodName, Token label) {
      return new ApplySuffix(
                 Token.NoToken,
                 label,
                 nameSeg("Guarantee" + methodName),
                 new List<ActualBinding>()
               );
    }

    private NameSegment callGamma(string v) {
      return nameSeg("Gamma_" + v);
    }
    private ApplySuffix callPolicy(string v) {
      return new ApplySuffix(Token.NoToken, null, nameSeg("L_"+v), new List<ActualBinding>());
    }

    private ApplySuffix callOrder(Expression leftVal, Expression rightVal) {
      return new ApplySuffix(
                 Token.NoToken,
                 null,
                 nameSeg("order"),
                 new List<ActualBinding>() {
                    new ActualBinding(null, nameSeg("lattice")),
                    new ActualBinding(null, leftVal),
                    new ActualBinding(null, rightVal) 
                 }
               );
    }

    private Expression calcGammaE(Expression e, ref InformationFlowState st) {
      HashSet<string> allVars = new HashSet<string>();
      getVariablesIn(e, ref allVars);
      if (allVars.Count == 0) {
        // Return lowest Sec value
        return lowestSec;
      }

      bool firstItem = true;
      Expression currReturn = lowestSec;
      Expression prevReturn = lowestSec;
      foreach (string v in allVars) {
        var name = v;
        if (st.parentMethod.Ins.Exists(x => x.Name == v)) {
          name = st.parentMethod.Name + "_In_" + v;
        } else if (st.parentMethod.Outs.Exists(x => x.Name == v)) {
          name = st.parentMethod.Name + "_return_" + v;
        }
        Expression policy;
        if (st.localVars.Contains(name)) {
          // Highest security policy
          policy = highestSec;
        } else {
          policy = callPolicy(name);
        }
        var meet = meetCall(callGamma(name), policy);
        if (firstItem) {
          prevReturn = meet;
          currReturn = meet;
          firstItem = false;
        } else {
          currReturn = joinCall(meet, prevReturn);
          prevReturn = currReturn;
        }
      }
      return currReturn;
    }

    private void getVariablesIn(Expression e, ref HashSet<string> currentVars) {
      switch(e) {
        case BinaryExpr bin:
          getVariablesIn(bin.E0, ref currentVars);
          getVariablesIn(bin.E1, ref currentVars);
          break;
        case NameSegment seg:
          currentVars.Add(seg.Name);
          break;
        case LiteralExpr:
          break;
        case NegationExpression neg:
          getVariablesIn(neg.E, ref currentVars);
          break;
        case UnaryOpExpr uOpExpr:
          getVariablesIn(uOpExpr.E, ref currentVars);
          break;
        //case SetDisplayExpr setExpr:
        //  //setExpr.Elements
        //  break;
        default:
          VisitUnknown(e, "Get Variables not defined for this node type yet.");
          break;
      }
    }
  }

}
