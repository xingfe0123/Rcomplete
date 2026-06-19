(* test_mathcomp.v *)
(* 测试 mathcomp-analysis 的 R^n 内积 API *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import realscale.
From mathcomp Require Import classical.
From mathcomp Require Import realalg.
From mathcomp Require Import topology.
From mathcomp Require Import normedtype.
From mathcomp Require Import sequences.
From mathcomp Require Import esum.

(* 测试 1: R^2 类型 *)
Check 'rV[R]_2.

(* 测试 2: 向量点积 *)
(* mathcomp 中行向量的点积用什么 notation? *)

(* 测试 3: 范数 *)
Check normr. (* 实数绝对值 *)

(* 测试 4: 列向量的内积 *)
(* 在 mathcomp 中, 'rV[R]_n 是列向量, 矩阵乘法表示线性映射 *)

(* 测试 5: 实数向量空间 *)
Check RVector.
