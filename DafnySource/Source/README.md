# Source Overview
The main bulk of code for the tool is defined in the `InformationFlowInjection.cs` file in the `Dafny` folder. This file defines a class called `InformationFlowVisitor` that handles the visiting of nodes in the Abstract Syntax Tree (AST). There are also some helper classes for modelling the state of the program, namely `InformationFlowState`, `InformationFlowVar` and `Lattice`.
Lattice is a behind the scenes implementation of the security lattice that is used to define the meet and join operator maps given the user defined lattice. 

The `InformationFlowVar` class models a variable in the program and tracks the actual variable, its security level and security policy. Keeping these vars updated during traversal of the AST also proved difficult. This class was originally inteded to handle local and Global vars, but ended up only handling Globals. Global variables are tracked in the `InformationFlowState` and so the `InformationFlowVar` class could be removed with some refactoring, and in some places, this has already ocurred.

The `InformationFlowState` class represents the global state of the program being modelled including globabl vars, control vars, the label number of the current statement, parent method, if the previos statement was a CAS statement and a list of global methods and functions. These are all updated and changed during traversal to allow necessary information about the program to be accessible during traversal and creation/injection of nodes.

The code visits nodes in the AST in a top-down manner using the visitor pattern. The implementation of this would ideally use double dispatch, but the native visitor pattern in Dafny does not use this, which makes it hard to implement. As a result, not every type of node has a visit method in the tool, as the tool only handles simpler programs. If a visit function
for a specific node does not exist, it will use the visit method for the nearest parent node, and should print a warning to the console.

The top-down manner is used so that the state of the program can be passed around.

#Modifications
If you wish to make modifications, note that the code is not perfect, and can definitiely be cleaned up and made more efficient.
To start modifying the project, open the `Dafny.sln` file. Set `DafnyDriver` as the startup project. Any code changes will happen within the `DafnyPipeline` project, but `DafnyDriver` is what needs to be run for debugging.
If you right-click the `DafnyDriver` project and select `Properties` it will open a menu, and if you select the `Debug` tab on the size, you can configue the Debug launch arguments. You can pass Dafny command line arguments here such as the file to run on, and any flags you want to use.

When working with code in the `InformationFlowInjector.cs` file and creating new nodes, there are helpful values as members of the `InformationFlowVisitor` class. There is a `secType` and `latticeType` that can be used when needing to create nodes of type `Sec` or `Lattice`.

There are comments throughout the code that should hopefully answer any further questions, and the code should otherwise be fairly easy to understand (hopefully).

## Issues You May Encounter
If creating a new `Function` or `Predicate` node, make sure to call `program.Builtins.CreateArrowTypeDecl(//number of params in your function)` after creation, so Dafny can create new arrow types. If this is forgotten, you will get a cryptic and hard to track error during Resolution.

Make sure to update the state as necessary before and after visiting a node.

When creating nodes, you should pass `Token.NoToken` to any `Token` parameters in a node constructor **except for `ActualBinding` expressions**. Pass `null` as the `Token` for `ActualBinding` otherwise you will get a long placeholder string when Dafny prints the code. 

If you get a yellow warning message in the console during use of the tool, it will be because a node in the AST does not have a visit method. To find out how to construct the node, the `Parser.cs` file is the best place to go. Note that it is not included in this repo, because it is generated automatically as part of the Dafny pipeline, when running the program, and should not be modified by a user.

Any other errors that pop-up in the Resolver or Translator during debugging will most likely be due to a newly created node being malformed in some way. Double check construction of the node in comparison to what happens in `Parser.cs`.
