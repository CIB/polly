; RUN: opt %loadPolly %defaultOpts  -polly-analyze-ir  -analyze < %s | FileCheck %s

; Check that array base addresses are invariant in the
; the considered region. In this code, only the inner
; loop (on j) should be modeled as a SCoP. Polly should not
; model A[i][j] as a read to A[i] and another read to
; X[j] (as X=A[i] changes with i).
;
; void ptr2ptr(float ** restrict A, int n) {
;     for (int i=0; i<n; ++i)
;         for (int j=0; j<2*n; ++j)
;             A[i][j] = i;
; }

target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define void @ptr2ptr(float** noalias %A, i32 %n) #0 {
entry:
  br label %entry.split

entry.split:                                      ; preds = %entry
  %cmp11 = icmp sgt i32 %n, 0
  br i1 %cmp11, label %for.cond1.preheader.lr.ph, label %for.end8.single_exit.single_exit

for.cond1.preheader.lr.ph:                        ; preds = %entry.split
  %0 = mul i32 %n, 2
  %1 = icmp sgt i32 %0, 1
  %smax16 = select i1 %1, i32 %0, i32 1
  %2 = add i32 %smax16, -1
  %3 = zext i32 %2 to i64
  %4 = add i64 %3, 1
  %5 = zext i32 %n to i64
  br label %for.cond1.preheader.single_entry

for.cond1.preheader.single_entry:                 ; preds = %for.inc6, %for.cond1.preheader.lr.ph
  %indvar18 = phi i64 [ %indvar.next, %for.inc6 ], [ 0, %for.cond1.preheader.lr.ph ]
  %i.012 = trunc i64 %indvar18 to i32
  %arrayidx = getelementptr float** %A, i64 %indvar18
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond1.preheader.single_entry
  %6 = trunc i32 %n to i31
  %cmp29 = icmp sgt i31 %6, 0
  br i1 %cmp29, label %for.body3.lr.ph, label %for.inc6.single_exit.single_exit

for.body3.lr.ph:                                  ; preds = %for.cond1.preheader
  br label %for.body3

for.body3:                                        ; preds = %for.body3.lr.ph, %for.body3
  %indvar = phi i64 [ 0, %for.body3.lr.ph ], [ %8, %for.body3 ]
  %conv = sitofp i32 %i.012 to float
  %7 = load float** %arrayidx, align 8
  %arrayidx5 = getelementptr float* %7, i64 %indvar
  store float %conv, float* %arrayidx5, align 4
  %8 = add i64 %indvar, 1
  %exitcond17 = icmp ne i64 %8, %4
  br i1 %exitcond17, label %for.body3, label %for.cond1.for.inc6_crit_edge

for.cond1.for.inc6_crit_edge:                     ; preds = %for.body3
  br label %for.inc6.single_exit.single_exit

for.inc6.single_exit.single_exit:                 ; preds = %for.cond1.for.inc6_crit_edge, %for.cond1.preheader
  br label %for.inc6.single_exit

for.inc6.single_exit:                             ; preds = %for.inc6.single_exit.single_exit
  br label %for.inc6

for.inc6:                                         ; preds = %for.inc6.single_exit
  %indvar.next = add i64 %indvar18, 1
  %exitcond = icmp ne i64 %indvar.next, %5
  br i1 %exitcond, label %for.cond1.preheader.single_entry, label %for.cond.for.end8_crit_edge

for.cond.for.end8_crit_edge:                      ; preds = %for.inc6
  br label %for.end8.single_exit.single_exit

for.end8.single_exit.single_exit:                 ; preds = %for.cond.for.end8_crit_edge, %entry.split
  br label %for.end8.single_exit

for.end8.single_exit:                             ; preds = %for.end8.single_exit.single_exit
  br label %for.end8

for.end8:                                         ; preds = %for.end8.single_exit
  ret void
}

; CHECK: Scop: for.cond1.preheader => for.inc6, Max Loop Depth: 1
