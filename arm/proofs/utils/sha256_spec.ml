(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Compatibility shim. The SHA-256 spec is architecture-agnostic and now *)
(* lives in common/ so both ARM and x86 proofs can share it.             *)

needs "common/sha256_spec.ml";;
