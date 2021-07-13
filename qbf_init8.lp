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
all(v24). all(v25). all(v26). all(v27). all(v28). all(v29). all(v30). all(v31). all(v32). all(v33). all(v34). all(v35). all(v36). all(v37). all(v38). all(v39). all(v40). all(v41). all(v42). all(v43). all(v44). all(v45). all(v46). 
neg(t1, v3). pos(t1, v6). pos(t1, v24). 
pos(t2, v2). neg(t2, v15). pos(t2, v24). 
pos(t3, v14). pos(t3, v21). pos(t3, v24). 
neg(t4, v15). neg(t4, v21). pos(t4, v24). 
pos(t5, v8). pos(t5, v23). neg(t5, v25). 
pos(t6, v5). pos(t6, v15). pos(t6, v26). 
neg(t7, v11). neg(t7, v15). pos(t7, v26). 
neg(t8, v12). pos(t8, v19). pos(t8, v26). 
neg(t9, v20). neg(t9, v21). neg(t9, v26). 
pos(t10, v8). neg(t10, v23). neg(t10, v26). 
pos(t11, v1). neg(t11, v2). pos(t11, v27). 
neg(t12, v9). pos(t12, v14). pos(t12, v27). 
neg(t13, v9). neg(t13, v23). neg(t13, v27). 
pos(t14, v21). neg(t14, v23). pos(t14, v28). 
pos(t15, v9). neg(t15, v10). neg(t15, v28). 
neg(t16, v11). neg(t16, v17). neg(t16, v28). 
neg(t17, v1). neg(t17, v6). neg(t17, v29). 
neg(t18, v7). pos(t18, v11). neg(t18, v29). 
pos(t19, v7). pos(t19, v13). neg(t19, v29). 
pos(t20, v4). pos(t20, v14). neg(t20, v29). 
pos(t21, v14). pos(t21, v19). neg(t21, v29). 
pos(t22, v14). pos(t22, v21). neg(t22, v29). 
pos(t23, v15). pos(t23, v23). pos(t23, v30). 
pos(t24, v3). neg(t24, v18). neg(t24, v30). 
neg(t25, v16). neg(t25, v22). neg(t25, v30). 
pos(t26, v7). pos(t26, v9). pos(t26, v31). 
neg(t27, v2). pos(t27, v15). pos(t27, v31). 
neg(t28, v1). neg(t28, v19). pos(t28, v31). 
neg(t29, v18). pos(t29, v21). neg(t29, v32). 
neg(t30, v16). neg(t30, v22). neg(t30, v32). 
neg(t31, v20). pos(t31, v23). neg(t31, v32). 
neg(t32, v1). neg(t32, v18). pos(t32, v33). 
pos(t33, v6). pos(t33, v14). neg(t33, v33). 
neg(t34, v13). pos(t34, v16). neg(t34, v33). 
pos(t35, v13). neg(t35, v22). neg(t35, v33). 
pos(t36, v6). neg(t36, v9). pos(t36, v34). 
pos(t37, v4). neg(t37, v11). pos(t37, v34). 
neg(t38, v10). neg(t38, v11). pos(t38, v34). 
neg(t39, v5). pos(t39, v12). pos(t39, v34). 
neg(t40, v15). neg(t40, v23). pos(t40, v34). 
neg(t41, v17). pos(t41, v23). neg(t41, v34). 
pos(t42, v4). neg(t42, v14). pos(t42, v35). 
neg(t43, v16). neg(t43, v17). pos(t43, v35). 
pos(t44, v10). neg(t44, v20). pos(t44, v35). 
pos(t45, v14). neg(t45, v22). pos(t45, v35). 
pos(t46, v6). neg(t46, v14). neg(t46, v35). 
pos(t47, v8). pos(t47, v17). neg(t47, v35). 
pos(t48, v14). neg(t48, v21). neg(t48, v35). 
pos(t49, v3). pos(t49, v20). pos(t49, v36). 
neg(t50, v5). neg(t50, v21). pos(t50, v36). 
neg(t51, v7). neg(t51, v14). pos(t51, v37). 
neg(t52, v11). pos(t52, v17). pos(t52, v37). 
neg(t53, v1). neg(t53, v18). neg(t53, v37). 
neg(t54, v20). neg(t54, v23). neg(t54, v37). 
neg(t55, v4). pos(t55, v5). pos(t55, v38). 
neg(t56, v5). neg(t56, v18). pos(t56, v38). 
pos(t57, v3). neg(t57, v13). neg(t57, v38). 
pos(t58, v13). pos(t58, v16). neg(t58, v38). 
pos(t59, v17). neg(t59, v22). pos(t59, v39). 
neg(t60, v8). neg(t60, v23). pos(t60, v39). 
neg(t61, v11). pos(t61, v20). neg(t61, v39). 
neg(t62, v13). neg(t62, v22). neg(t62, v39). 
neg(t63, v14). pos(t63, v15). pos(t63, v40). 
pos(t64, v9). pos(t64, v16). pos(t64, v40). 
pos(t65, v9). neg(t65, v11). neg(t65, v40). 
neg(t66, v3). neg(t66, v14). neg(t66, v40). 
neg(t67, v9). pos(t67, v16). neg(t67, v40). 
pos(t68, v12). pos(t68, v16). neg(t68, v40). 
neg(t69, v12). neg(t69, v17). neg(t69, v40). 
neg(t70, v7). neg(t70, v22). neg(t70, v40). 
pos(t71, v6). neg(t71, v22). pos(t71, v41). 
neg(t72, v15). pos(t72, v23). pos(t72, v41). 
pos(t73, v4). pos(t73, v7). neg(t73, v41). 
pos(t74, v4). pos(t74, v19). neg(t74, v41). 
pos(t75, v7). pos(t75, v11). pos(t75, v42). 
pos(t76, v5). neg(t76, v12). pos(t76, v42). 
neg(t77, v8). pos(t77, v13). pos(t77, v42). 
pos(t78, v13). neg(t78, v15). pos(t78, v42). 
neg(t79, v10). pos(t79, v16). pos(t79, v42). 
neg(t80, v10). pos(t80, v17). pos(t80, v42). 
neg(t81, v10). neg(t81, v19). pos(t81, v42). 
pos(t82, v4). pos(t82, v5). neg(t82, v42). 
neg(t83, v3). neg(t83, v11). neg(t83, v42). 
pos(t84, v16). neg(t84, v17). neg(t84, v42). 
neg(t85, v6). neg(t85, v7). pos(t85, v43). 
neg(t86, v7). neg(t86, v13). pos(t86, v43). 
pos(t87, v1). pos(t87, v19). pos(t87, v43). 
neg(t88, v14). pos(t88, v19). pos(t88, v43). 
neg(t89, v4). neg(t89, v5). neg(t89, v43). 
neg(t90, v1). neg(t90, v16). neg(t90, v43). 
neg(t91, v6). neg(t91, v8). pos(t91, v44). 
pos(t92, v8). pos(t92, v20). pos(t92, v44). 
neg(t93, v4). pos(t93, v5). neg(t93, v44). 
neg(t94, v4). pos(t94, v10). neg(t94, v44). 
neg(t95, v6). neg(t95, v13). neg(t95, v44). 
pos(t96, v13). neg(t96, v20). neg(t96, v44). 
pos(t97, v2). pos(t97, v12). neg(t97, v45). 
pos(t98, v1). pos(t98, v19). neg(t98, v45). 
neg(t99, v11). pos(t99, v12). neg(t99, v46). 
neg(t100, v12). pos(t100, v18). neg(t100, v46). 
