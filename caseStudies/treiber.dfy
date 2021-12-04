// include "utils.dfy"
// import opened Utils
datatype Sec = Low | High
datatype Node = Node(next: Node, value: int, level: Sec) | Nil 
// module Utils {
    // datatype Sec = High | Low
    // class Node<V> {
    //     ghost var Repr: set<object>;
    //     ghost var nodes: set<Node?<V>>;
    //     ghost var values: seq<V>;

    //     var val: V;
    //     var next: Node?<V>; 
    //     var level: Sec
        
    //     predicate Valid()
    //         reads this, Repr, next, nodes
    //         decreases nodes
    //     {
    //         this in Repr &&
    //         // this in nodes &&
    //         null !in nodes && 
    //         (next == null ==> nodes == {this} && values == [val]) &&
    //         (next != null ==> next in nodes && 
    //                             nodes == {this} + next.nodes &&
    //                             this !in next.nodes &&
    //                             values == [val] + next.values //&&
    //                             // next.Valid()         
    //         )    
    //     }

    //     constructor Cons(value: V, level: Sec)
    //         ensures Valid()
    //         ensures fresh(Repr)
    //         ensures nodes == {this}
    //         ensures values == [value]

    //     {   
    //         val := value;
    //         next := null;
    //         this.level := level;

    //         values := [value];
    //         nodes := {this};
    //         Repr := {this};
    //     }
    // }
// }
// type Value
// datatype Level = High | Low
// datatype Node<Value> = Nil | Node(val: Value, next: Node<Value>, level: Level)

// import opened Utils


// datatype Sec = High | Low

type Lattice = map<Sec, set<Sec>>

class Treiber {
    var head: Node;   

    method put(v: int, level: Sec)
        modifies this
        decreases *
    {
        var n := Node(Nil, v, level);
        var ss: Node;

        // Do
        ss := this.head;
        n := n.(next := ss);
        // //While
        var b;
        b, this.head := CAS<Node>(this.head, ss, n);
        while (!b) 
            decreases *
        {
            ss := this.head;
            n := n.(next := ss);
        }
    }

    method pop() returns (v: int)
        modifies this
        decreases *
    {
        var level: Sec;
        var exit := 0;
        var ss, ssn, n: Node;   
        // v := V;
        // do
        ss := head;
        if (!ss.Nil?) {
            level := ss.level;
            if (level.Low?) {
                ssn := ss.next;
                v := ss.value;
                var b;
                b, head := CAS<Node>(head, ss, ssn);
                if (b) {
                    exit := 1;
                }
            }
        }

        //while
        while (exit == 0) 
            decreases *
        {
            ss := head;
            if (!ss.Nil?) {
                level := ss.level;
                if (level == Low) {
                    ssn := ss.next;
                    v := ss.value;
                    var b;
                    b, head := CAS<Node>(head, ss, ssn);
                    if (b) {
                        exit := 1;
                    }
                }
            }
        }
    }
}

method CAS<T(==)>(x: T, e1: T, e2: T)
    returns (b: bool, x2: T)
  ensures x == e1 ==> x2 == e2 && b
  ensures x != e1 ==> x2 == x && !b
{
  if x == e1 {
    x2 := e2;
    b := true;
  } else {
    x2 := x;
    b := false;
  }
}