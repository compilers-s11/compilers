; ModuleID = 'sum.o'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64"
target triple = "x86_64-apple-darwin10.6"

define i32 @_Z3sumii(i32 %a, i32 %b) nounwind ssp {
entry:
  %a_addr = alloca i32
  %b_addr = alloca i32
  %retval = alloca i32
  %0 = alloca i32
  %i = alloca i32
  %res = alloca i32
  %"alloca point" = bitcast i32 0 to i32
  store i32 %a, i32* %a_addr
  store i32 %b, i32* %b_addr
  store i32 1, i32* %res, align 4
  %1 = load i32* %a_addr, align 4
  store i32 %1, i32* %i, align 4
  br label %bb1

bb:                                               ; preds = %bb1
  %2 = load i32* %res, align 4
  %3 = load i32* %i, align 4
  %4 = mul nsw i32 %2, %3
  store i32 %4, i32* %res, align 4
  %5 = load i32* %i, align 4
  %6 = add nsw i32 %5, 1
  store i32 %6, i32* %i, align 4
  br label %bb1

bb1:                                              ; preds = %bb, %entry
  %7 = load i32* %i, align 4
  %8 = load i32* %b_addr, align 4
  %9 = icmp slt i32 %7, %8
  br i1 %9, label %bb, label %bb2

bb2:                                              ; preds = %bb1
  %10 = load i32* %res, align 4
  store i32 %10, i32* %0, align 4
  %11 = load i32* %0, align 4
  store i32 %11, i32* %retval, align 4
  br label %return

return:                                           ; preds = %bb2
  %retval3 = load i32* %retval
  ret i32 %retval3
}
