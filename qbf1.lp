%input predicates:
%pos(C,V) -> variable V occurs positively within DNF TERM C
%neg(C,V) -> variable V occurs negatively within DNF TERM C
%all(V) -> all quantified variable

t(V) | f(V) :- pos(_,V).
t(V) | f(V) :- neg(_,V).

t(V) :- sat, all(V).
f(V) :- sat, all(V).

:- not sat.

sat(C,V) :- pos(C,V), t(V).
sat(C,V) :- neg(C,V), f(V).

sat :- sat(C,V1), sat(C,V2), sat(C,V3), V1 < V2, V2 < V3.

all(v23). all(v24). all(v25). all(v26). all(v27). all(v28). all(v29). all(v30). all(v31). all(v32). all(v33). all(v34). all(v35). all(v36). all(v37). all(v38). all(v39). all(v40). all(v41). all(v42). all(v43). all(v44). 
neg(t1, v6). neg(t1, v9). pos(t1, v23). 
neg(t2, v6). neg(t2, v13). pos(t2, v23). 
pos(t3, v13). pos(t3, v21). pos(t3, v23). 
neg(t4, v19). neg(t4, v21). pos(t4, v23). 
neg(t5, v15). pos(t5, v17). neg(t5, v23). 
neg(t6, v2). neg(t6, v6). pos(t6, v24). 
neg(t7, v3). neg(t7, v10). pos(t7, v24). 
pos(t8, v12). neg(t8, v17). pos(t8, v24). 
pos(t9, v18). neg(t9, v20). pos(t9, v24). 
pos(t10, v1). pos(t10, v14). neg(t10, v24). 
pos(t11, v13). neg(t11, v14). neg(t11, v24). 
neg(t12, v11). neg(t12, v13). pos(t12, v25). 
neg(t13, v1). neg(t13, v15). pos(t13, v25). 
neg(t14, v1). pos(t14, v12). pos(t14, v26). 
pos(t15, v13). neg(t15, v16). pos(t15, v26). 
pos(t16, v8). neg(t16, v18). pos(t16, v26). 
neg(t17, v17). neg(t17, v19). pos(t17, v26). 
neg(t18, v2). neg(t18, v14). neg(t18, v26). 
neg(t19, v15). pos(t19, v17). neg(t19, v26). 
pos(t20, v4). pos(t20, v7). pos(t20, v27). 
pos(t21, v6). pos(t21, v19). pos(t21, v27). 
pos(t22, v10). pos(t22, v17). neg(t22, v27). 
pos(t23, v11). neg(t23, v18). neg(t23, v27). 
neg(t24, v4). pos(t24, v7). pos(t24, v28). 
pos(t25, v7). neg(t25, v12). pos(t25, v28). 
pos(t26, v5). neg(t26, v19). pos(t26, v29). 
pos(t27, v6). neg(t27, v20). pos(t27, v29). 
neg(t28, v7). pos(t28, v22). pos(t28, v30). 
neg(t29, v12). pos(t29, v22). neg(t29, v30). 
neg(t30, v3). pos(t30, v9). pos(t30, v31). 
pos(t31, v5). pos(t31, v10). pos(t31, v31). 
neg(t32, v1). pos(t32, v4). neg(t32, v31). 
neg(t33, v6). neg(t33, v19). pos(t33, v32). 
pos(t34, v20). pos(t34, v22). pos(t34, v32). 
pos(t35, v7). neg(t35, v20). neg(t35, v32). 
neg(t36, v4). pos(t36, v21). neg(t36, v32). 
pos(t37, v9). neg(t37, v21). neg(t37, v32). 
neg(t38, v4). pos(t38, v8). pos(t38, v33). 
neg(t39, v1). neg(t39, v5). neg(t39, v33). 
pos(t40, v4). neg(t40, v5). neg(t40, v33). 
neg(t41, v10). pos(t41, v14). neg(t41, v33). 
pos(t42, v10). pos(t42, v18). neg(t42, v33). 
neg(t43, v17). neg(t43, v19). neg(t43, v33). 
pos(t44, v3). pos(t44, v22). neg(t44, v33). 
pos(t45, v2). neg(t45, v11). pos(t45, v34). 
neg(t46, v15). pos(t46, v16). pos(t46, v34). 
pos(t47, v6). neg(t47, v17). pos(t47, v34). 
pos(t48, v14). neg(t48, v20). pos(t48, v34). 
neg(t49, v2). pos(t49, v6). neg(t49, v34). 
pos(t50, v14). neg(t50, v15). neg(t50, v34). 
pos(t51, v10). pos(t51, v18). neg(t51, v34). 
neg(t52, v12). neg(t52, v21). neg(t52, v34). 
pos(t53, v6). neg(t53, v10). pos(t53, v35). 
neg(t54, v1). pos(t54, v10). neg(t54, v35). 
pos(t55, v15). pos(t55, v17). neg(t55, v35). 
pos(t56, v14). neg(t56, v17). neg(t56, v35). 
pos(t57, v13). pos(t57, v18). neg(t57, v35). 
neg(t58, v6). pos(t58, v8). pos(t58, v36). 
neg(t59, v2). pos(t59, v10). pos(t59, v36). 
pos(t60, v9). neg(t60, v14). pos(t60, v36). 
pos(t61, v15). pos(t61, v19). pos(t61, v36). 
pos(t62, v16). pos(t62, v21). pos(t62, v36). 
neg(t63, v13). neg(t63, v22). pos(t63, v36). 
pos(t64, v2). neg(t64, v8). neg(t64, v36). 
neg(t65, v11). neg(t65, v16). neg(t65, v36). 
pos(t66, v2). neg(t66, v8). pos(t66, v37). 
neg(t67, v11). neg(t67, v13). neg(t67, v37). 
pos(t68, v4). neg(t68, v16). neg(t68, v37). 
pos(t69, v9). pos(t69, v11). pos(t69, v38). 
neg(t70, v5). pos(t70, v10). neg(t70, v38). 
pos(t71, v5). pos(t71, v11). pos(t71, v39). 
neg(t72, v4). neg(t72, v16). pos(t72, v39). 
pos(t73, v3). pos(t73, v17). pos(t73, v39). 
pos(t74, v6). pos(t74, v17). pos(t74, v39). 
neg(t75, v16). pos(t75, v19). pos(t75, v39). 
pos(t76, v2). neg(t76, v6). neg(t76, v39). 
neg(t77, v9). neg(t77, v13). neg(t77, v39). 
neg(t78, v16). pos(t78, v20). neg(t78, v39). 
pos(t79, v2). pos(t79, v7). pos(t79, v40). 
neg(t80, v6). neg(t80, v11). pos(t80, v40). 
neg(t81, v2). neg(t81, v10). neg(t81, v40). 
neg(t82, v13). neg(t82, v16). neg(t82, v40). 
neg(t83, v7). pos(t83, v18). neg(t83, v40). 
pos(t84, v4). neg(t84, v14). pos(t84, v41). 
neg(t85, v4). neg(t85, v14). pos(t85, v41). 
pos(t86, v7). pos(t86, v17). neg(t86, v41). 
pos(t87, v13). pos(t87, v20). neg(t87, v41). 
neg(t88, v6). pos(t88, v10). pos(t88, v42). 
pos(t89, v12). neg(t89, v13). neg(t89, v42). 
neg(t90, v2). pos(t90, v14). neg(t90, v42). 
pos(t91, v5). neg(t91, v18). neg(t91, v42). 
pos(t92, v3). neg(t92, v7). neg(t92, v43). 
pos(t93, v8). neg(t93, v16). neg(t93, v43). 
neg(t94, v1). neg(t94, v19). neg(t94, v43). 
pos(t95, v6). pos(t95, v13). pos(t95, v44). 
pos(t96, v14). neg(t96, v20). pos(t96, v44). 
pos(t97, v7). pos(t97, v13). neg(t97, v44). 
neg(t98, v3). pos(t98, v17). neg(t98, v44). 
pos(t99, v7). pos(t99, v19). neg(t99, v44). 
neg(t100, v10). neg(t100, v21). neg(t100, v44).