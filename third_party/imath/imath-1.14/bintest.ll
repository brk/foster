; ModuleID = 'bintest.c'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"
target triple = "i386-pc-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }
%struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }
%struct.mpz = type { i16, i16*, i32, i32, i8 }

@stderr = external global %struct._IO_FILE*       ; <%struct._IO_FILE**> [#uses=1]
@.str = private constant [24 x i8] c"Usage: bintest <value>\0A\00" ; <[24 x i8]*> [#uses=1]
@.str1 = private constant [44 x i8] c"Result code from mp_int_read_string() = %d\0A\00" ; <[44 x i8]*> [#uses=1]
@.str2 = private constant [56 x i8] c"%d bytes needed to write this value in 2's complement.\0A\00" ; <[56 x i8]*> [#uses=1]
@.str3 = private constant [42 x i8] c"Result code from mp_int_to_binary() = %d\0A\00" ; <[42 x i8]*> [#uses=1]
@MP_OK = external constant i32                    ; <i32*> [#uses=4]
@.str4 = private constant [4 x i8] c"%d.\00"      ; <[4 x i8]*> [#uses=1]
@.str5 = private constant [4 x i8] c"%d\0A\00"    ; <[4 x i8]*> [#uses=1]
@.str6 = private constant [44 x i8] c"Result code from mp_int_read_binary() = %d\0A\00" ; <[44 x i8]*> [#uses=1]
@.str7 = private constant [7 x i8] c"[%s]\0A\0A\00" ; <[7 x i8]*> [#uses=1]
@.str8 = private constant [50 x i8] c"%d bytes needed to write this value as unsigned.\0A\00" ; <[50 x i8]*> [#uses=1]
@.str9 = private constant [44 x i8] c"Result code from mp_int_to_unsigned() = %d\0A\00" ; <[44 x i8]*> [#uses=1]
@.str10 = private constant [46 x i8] c"Result code from mp_int_read_unsigned() = %d\0A\00" ; <[46 x i8]*> [#uses=1]

define i32 @main(i32 %argc, i8** %argv) nounwind {
  %1 = alloca i32, align 4                        ; <i32*> [#uses=6]
  %2 = alloca i32, align 4                        ; <i32*> [#uses=2]
  %3 = alloca i8**, align 4                       ; <i8***> [#uses=3]
  %buf = alloca [512 x i8], align 1               ; <[512 x i8]*> [#uses=12]
  %v = alloca %struct.mpz, align 4                ; <%struct.mpz*> [#uses=7]
  %w = alloca %struct.mpz, align 4                ; <%struct.mpz*> [#uses=6]
  %res = alloca i32, align 4                      ; <i32*> [#uses=14]
  %len = alloca i32, align 4                      ; <i32*> [#uses=8]
  %ix = alloca i32, align 4                       ; <i32*> [#uses=6]
  %ix1 = alloca i32, align 4                      ; <i32*> [#uses=6]
  store i32 0, i32* %1
  store i32 %argc, i32* %2
  store i8** %argv, i8*** %3
  %4 = load i32* %2                               ; <i32> [#uses=1]
  %5 = icmp slt i32 %4, 2                         ; <i1> [#uses=1]
  br i1 %5, label %14, label %6

; <label>:6                                       ; preds = %0
  %7 = load i8*** %3                              ; <i8**> [#uses=1]
  %8 = getelementptr inbounds i8** %7, i32 1      ; <i8**> [#uses=1]
  %9 = load i8** %8                               ; <i8*> [#uses=1]
  %10 = getelementptr inbounds i8* %9, i32 0      ; <i8*> [#uses=1]
  %11 = load i8* %10                              ; <i8> [#uses=1]
  %12 = sext i8 %11 to i32                        ; <i32> [#uses=1]
  %13 = icmp eq i32 %12, 0                        ; <i1> [#uses=1]
  br i1 %13, label %14, label %17

; <label>:14                                      ; preds = %6, %0
  %15 = load %struct._IO_FILE** @stderr           ; <%struct._IO_FILE*> [#uses=1]
  %16 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %15, i8* getelementptr inbounds ([24 x i8]* @.str, i32 0, i32 0)) ; <i32> [#uses=0]
  store i32 1, i32* %1
  br label %124

; <label>:17                                      ; preds = %6
  %18 = call i32 @mp_int_init(%struct.mpz* %v)    ; <i32> [#uses=0]
  %19 = call i32 @mp_int_init(%struct.mpz* %w)    ; <i32> [#uses=0]
  %20 = load i8*** %3                             ; <i8**> [#uses=1]
  %21 = getelementptr inbounds i8** %20, i32 1    ; <i8**> [#uses=1]
  %22 = load i8** %21                             ; <i8*> [#uses=1]
  %23 = call i32 @mp_int_read_string(%struct.mpz* %v, i32 10, i8* %22) ; <i32> [#uses=1]
  store i32 %23, i32* %res
  %24 = load i32* %res                            ; <i32> [#uses=1]
  %25 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([44 x i8]* @.str1, i32 0, i32 0), i32 %24) ; <i32> [#uses=0]
  %26 = call i32 @mp_int_binary_len(%struct.mpz* %v) ; <i32> [#uses=1]
  store i32 %26, i32* %len
  %27 = load i32* %len                            ; <i32> [#uses=1]
  %28 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([56 x i8]* @.str2, i32 0, i32 0), i32 %27) ; <i32> [#uses=0]
  %29 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %30 = call i32 @mp_int_to_binary(%struct.mpz* %v, i8* %29, i32 512) ; <i32> [#uses=1]
  store i32 %30, i32* %res
  %31 = load i32* %res                            ; <i32> [#uses=1]
  %32 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([42 x i8]* @.str3, i32 0, i32 0), i32 %31) ; <i32> [#uses=0]
  %33 = load i32* %res                            ; <i32> [#uses=1]
  %34 = load i32* @MP_OK                          ; <i32> [#uses=1]
  %35 = icmp eq i32 %33, %34                      ; <i1> [#uses=1]
  br i1 %35, label %36, label %59

; <label>:36                                      ; preds = %17
  store i32 0, i32* %ix
  br label %37

; <label>:37                                      ; preds = %49, %36
  %38 = load i32* %ix                             ; <i32> [#uses=1]
  %39 = load i32* %len                            ; <i32> [#uses=1]
  %40 = sub i32 %39, 1                            ; <i32> [#uses=1]
  %41 = icmp slt i32 %38, %40                     ; <i1> [#uses=1]
  br i1 %41, label %42, label %52

; <label>:42                                      ; preds = %37
  %43 = load i32* %ix                             ; <i32> [#uses=1]
  %44 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %45 = getelementptr inbounds i8* %44, i32 %43   ; <i8*> [#uses=1]
  %46 = load i8* %45                              ; <i8> [#uses=1]
  %47 = zext i8 %46 to i32                        ; <i32> [#uses=1]
  %48 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str4, i32 0, i32 0), i32 %47) ; <i32> [#uses=0]
  br label %49

; <label>:49                                      ; preds = %42
  %50 = load i32* %ix                             ; <i32> [#uses=1]
  %51 = add nsw i32 %50, 1                        ; <i32> [#uses=1]
  store i32 %51, i32* %ix
  br label %37

; <label>:52                                      ; preds = %37
  %53 = load i32* %ix                             ; <i32> [#uses=1]
  %54 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %55 = getelementptr inbounds i8* %54, i32 %53   ; <i8*> [#uses=1]
  %56 = load i8* %55                              ; <i8> [#uses=1]
  %57 = zext i8 %56 to i32                        ; <i32> [#uses=1]
  %58 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str5, i32 0, i32 0), i32 %57) ; <i32> [#uses=0]
  br label %60

; <label>:59                                      ; preds = %17
  store i32 1, i32* %1
  br label %124

; <label>:60                                      ; preds = %52
  %61 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %62 = load i32* %len                            ; <i32> [#uses=1]
  %63 = call i32 @mp_int_read_binary(%struct.mpz* %w, i8* %61, i32 %62) ; <i32> [#uses=1]
  store i32 %63, i32* %res
  %64 = load i32* %res                            ; <i32> [#uses=1]
  %65 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([44 x i8]* @.str6, i32 0, i32 0), i32 %64) ; <i32> [#uses=0]
  %66 = load i32* %res                            ; <i32> [#uses=1]
  %67 = load i32* @MP_OK                          ; <i32> [#uses=1]
  %68 = icmp eq i32 %66, %67                      ; <i1> [#uses=1]
  br i1 %68, label %69, label %74

; <label>:69                                      ; preds = %60
  %70 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %71 = call i32 @mp_int_to_string(%struct.mpz* %w, i32 10, i8* %70, i32 512) ; <i32> [#uses=0]
  %72 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %73 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([7 x i8]* @.str7, i32 0, i32 0), i8* %72) ; <i32> [#uses=0]
  br label %74

; <label>:74                                      ; preds = %69, %60
  %75 = call i32 @mp_int_unsigned_len(%struct.mpz* %v) ; <i32> [#uses=1]
  store i32 %75, i32* %len
  %76 = load i32* %len                            ; <i32> [#uses=1]
  %77 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([50 x i8]* @.str8, i32 0, i32 0), i32 %76) ; <i32> [#uses=0]
  %78 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %79 = call i32 @mp_int_to_unsigned(%struct.mpz* %v, i8* %78, i32 512) ; <i32> [#uses=1]
  store i32 %79, i32* %res
  %80 = load i32* %res                            ; <i32> [#uses=1]
  %81 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([44 x i8]* @.str9, i32 0, i32 0), i32 %80) ; <i32> [#uses=0]
  %82 = load i32* %res                            ; <i32> [#uses=1]
  %83 = load i32* @MP_OK                          ; <i32> [#uses=1]
  %84 = icmp eq i32 %82, %83                      ; <i1> [#uses=1]
  br i1 %84, label %85, label %108

; <label>:85                                      ; preds = %74
  store i32 0, i32* %ix1
  br label %86

; <label>:86                                      ; preds = %98, %85
  %87 = load i32* %ix1                            ; <i32> [#uses=1]
  %88 = load i32* %len                            ; <i32> [#uses=1]
  %89 = sub i32 %88, 1                            ; <i32> [#uses=1]
  %90 = icmp slt i32 %87, %89                     ; <i1> [#uses=1]
  br i1 %90, label %91, label %101

; <label>:91                                      ; preds = %86
  %92 = load i32* %ix1                            ; <i32> [#uses=1]
  %93 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %94 = getelementptr inbounds i8* %93, i32 %92   ; <i8*> [#uses=1]
  %95 = load i8* %94                              ; <i8> [#uses=1]
  %96 = zext i8 %95 to i32                        ; <i32> [#uses=1]
  %97 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str4, i32 0, i32 0), i32 %96) ; <i32> [#uses=0]
  br label %98

; <label>:98                                      ; preds = %91
  %99 = load i32* %ix1                            ; <i32> [#uses=1]
  %100 = add nsw i32 %99, 1                       ; <i32> [#uses=1]
  store i32 %100, i32* %ix1
  br label %86

; <label>:101                                     ; preds = %86
  %102 = load i32* %ix1                           ; <i32> [#uses=1]
  %103 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %104 = getelementptr inbounds i8* %103, i32 %102 ; <i8*> [#uses=1]
  %105 = load i8* %104                            ; <i8> [#uses=1]
  %106 = zext i8 %105 to i32                      ; <i32> [#uses=1]
  %107 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str5, i32 0, i32 0), i32 %106) ; <i32> [#uses=0]
  br label %109

; <label>:108                                     ; preds = %74
  store i32 1, i32* %1
  br label %124

; <label>:109                                     ; preds = %101
  %110 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %111 = load i32* %len                           ; <i32> [#uses=1]
  %112 = call i32 @mp_int_read_unsigned(%struct.mpz* %w, i8* %110, i32 %111) ; <i32> [#uses=1]
  store i32 %112, i32* %res
  %113 = load i32* %res                           ; <i32> [#uses=1]
  %114 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([46 x i8]* @.str10, i32 0, i32 0), i32 %113) ; <i32> [#uses=0]
  %115 = load i32* %res                           ; <i32> [#uses=1]
  %116 = load i32* @MP_OK                         ; <i32> [#uses=1]
  %117 = icmp eq i32 %115, %116                   ; <i1> [#uses=1]
  br i1 %117, label %118, label %123

; <label>:118                                     ; preds = %109
  %119 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %120 = call i32 @mp_int_to_string(%struct.mpz* %w, i32 10, i8* %119, i32 512) ; <i32> [#uses=0]
  %121 = getelementptr inbounds [512 x i8]* %buf, i32 0, i32 0 ; <i8*> [#uses=1]
  %122 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([7 x i8]* @.str7, i32 0, i32 0), i8* %121) ; <i32> [#uses=0]
  br label %123

; <label>:123                                     ; preds = %118, %109
  call void @mp_int_clear(%struct.mpz* %v)
  call void @mp_int_clear(%struct.mpz* %w)
  store i32 0, i32* %1
  br label %124

; <label>:124                                     ; preds = %123, %108, %59, %14
  %125 = load i32* %1                             ; <i32> [#uses=1]
  ret i32 %125
}

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...)

declare i32 @mp_int_init(%struct.mpz*)

declare i32 @mp_int_read_string(%struct.mpz*, i32, i8*)

declare i32 @printf(i8*, ...)

declare i32 @mp_int_binary_len(%struct.mpz*)

declare i32 @mp_int_to_binary(%struct.mpz*, i8*, i32)

declare i32 @mp_int_read_binary(%struct.mpz*, i8*, i32)

declare i32 @mp_int_to_string(%struct.mpz*, i32, i8*, i32)

declare i32 @mp_int_unsigned_len(%struct.mpz*)

declare i32 @mp_int_to_unsigned(%struct.mpz*, i8*, i32)

declare i32 @mp_int_read_unsigned(%struct.mpz*, i8*, i32)

declare void @mp_int_clear(%struct.mpz*)
