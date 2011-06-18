Compiled Code Snippets
======================

Until, implemented with functions and pattern matching
------------------------------------------------------

LLVM assembly for this code::

  hof-until-case = { c : {i1} => b : { () } =>
    case c ()
      of true ->  0
      of false -> b (); hof-until-case c b
    end
  };

is as follows::

  define fastcc i32 @hof-until-case(%8 %"c!35", %9 %"b!36") gc "fostergc" {
  entry:
    %case_slot = alloca i32                                     ; #uses = 3	; i32*
    %stackref2 = alloca %9*                                     ; #uses = 4	; { void (i8*)*, i8* }**
    %ptrfromnonptr1 = alloca %9                                 ; #uses = 2	; { void (i8*)*, i8* }*
    %stackref = alloca %8*                                      ; #uses = 4	; { i1 (i8*)*, i8* }**
    %ptrfromnonptr = alloca %8                                  ; #uses = 2	; { i1 (i8*)*, i8* }*
    store %8 %"c!35", %8* %ptrfromnonptr
    %gcroot = bitcast %8** %stackref to i8**, !fostergcroot !3  ; #uses = 1	; i8**
    call void @llvm.gcroot(i8** %gcroot, i8* bitcast (%3* @__foster_typemap_gcatom1 to i8*)), !willnotgc !2
    store %8* %ptrfromnonptr, %8** %stackref
    store %9 %"b!36", %9* %ptrfromnonptr1
    %gcroot3 = bitcast %9** %stackref2 to i8**, !fostergcroot !3 ; #uses = 1	; i8**
    call void @llvm.gcroot(i8** %gcroot3, i8* bitcast (%3* @__foster_typemap_gcatom1 to i8*)), !willnotgc !2
    store %9* %ptrfromnonptr1, %9** %stackref2
    %autoload = load %8** %stackref                             ; #uses = 2	; { i1 (i8*)*, i8* }*
    %getCloEnv.subgep = getelementptr %8* %autoload, i32 0, i32 1 ; #uses = 1	; i8**
    %subgep_ld = load i8** %getCloEnv.subgep                    ; #uses = 1	; i8*
    %getCloCode.subgep = getelementptr %8* %autoload, i32 0, i32 0 ; #uses = 1	; i1 (i8*)**
    %subgep_ld4 = load i1 (i8*)** %getCloCode.subgep            ; #uses = 1	; i1 (i8*)*
    %".x!29" = tail call fastcc i1 %subgep_ld4(i8* %subgep_ld)  ; #uses = 1	; i1
    switch i1 %".x!29", label %case_end [
      i1 false, label %casetest_0
      i1 true, label %casetest_1
    ]

  casetest_0:                                       ; preds = %entry
    %autoload5 = load %9** %stackref2                           ; #uses = 2	; { void (i8*)*, i8* }*
    %getCloEnv.subgep6 = getelementptr %9* %autoload5, i32 0, i32 1 ; #uses = 1	; i8**
    %subgep_ld7 = load i8** %getCloEnv.subgep6                  ; #uses = 1	; i8*
    %getCloCode.subgep8 = getelementptr %9* %autoload5, i32 0, i32 0 ; #uses = 1	; void (i8*)**
    %subgep_ld9 = load void (i8*)** %getCloCode.subgep8         ; #uses = 1	; void (i8*)*
    tail call fastcc void %subgep_ld9(i8* %subgep_ld7)
    %autoload10 = load %8** %stackref                           ; #uses = 1	; { i1 (i8*)*, i8* }*
    %loadStructParam = load %8* %autoload10                     ; #uses = 1	; { i1 (i8*)*, i8* }
    %autoload11 = load %9** %stackref2                          ; #uses = 1	; { void (i8*)*, i8* }*
    %loadStructParam12 = load %9* %autoload11                   ; #uses = 1	; { void (i8*)*, i8* }
    %calltmp = tail call fastcc i32 @hof-until-case(%8 %loadStructParam, %9 %loadStructParam12) ; #uses = 1	; i32
    store i32 %calltmp, i32* %case_slot
    br label %case_end

  casetest_1:                                       ; preds = %entry
    store i32 0, i32* %case_slot
    br label %case_end

  case_end:                                         ; preds = %casetest_1, %casetest_0, %entry
    %.case = load i32* %case_slot                               ; #uses = 1	; i32
    ret i32 %.case
  }

which gets optimized to this. Note that LLVM IR optimizations turn ``switch`` into ``br``.
Also note that the tail recursion isn't turned into a CFG loop (yet)::

  define fastcc i32 @hof-until-case(%2 %"c!35", %3 %"b!36") gc "fostergc" {
  entry:
    %stackref2 = alloca %3*, align 4                            ; #uses = 2	; { void (i8*)*, i8* }**
    %ptrfromnonptr1 = alloca %3, align 8                        ; #uses = 5	; { void (i8*)*, i8* }*
    %stackref = alloca %2*, align 4                             ; #uses = 3	; { i1 (i8*)*, i8* }**
    %ptrfromnonptr = alloca %2, align 8                         ; #uses = 2	; { i1 (i8*)*, i8* }*
    store %2 %"c!35", %2* %ptrfromnonptr, align 8
    %gcroot = bitcast %2** %stackref to i8**, !fostergcroot !3  ; #uses = 1	; i8**
    call void @llvm.gcroot(i8** %gcroot, i8* bitcast (%0* @__foster_typemap_gcatom1 to i8*)), !willnotgc !2
    store %2* %ptrfromnonptr, %2** %stackref, align 4
    store %3 %"b!36", %3* %ptrfromnonptr1, align 8
    %gcroot3 = bitcast %3** %stackref2 to i8**, !fostergcroot !3 ; #uses = 1	; i8**
    call void @llvm.gcroot(i8** %gcroot3, i8* bitcast (%0* @__foster_typemap_gcatom1 to i8*)), !willnotgc !2
    store %3* %ptrfromnonptr1, %3** %stackref2, align 4
    %autoload = load %2** %stackref, align 4                    ; #uses = 3	; { i1 (i8*)*, i8* }*
    %getCloEnv.subgep = getelementptr %2* %autoload, i32 0, i32 1 ; #uses = 1	; i8**
    %subgep_ld = load i8** %getCloEnv.subgep, align 4           ; #uses = 1	; i8*
    %getCloCode.subgep = getelementptr %2* %autoload, i32 0, i32 0 ; #uses = 1	; i1 (i8*)**
    %subgep_ld4 = load i1 (i8*)** %getCloCode.subgep, align 4   ; #uses = 1	; i1 (i8*)*
    %".x!29" = tail call fastcc i1 %subgep_ld4(i8* %subgep_ld)  ; #uses = 1	; i1
    br i1 %".x!29", label %case_end, label %casetest_0

  casetest_0:                                       ; preds = %entry
    %getCloEnv.subgep6 = getelementptr %3* %ptrfromnonptr1, i32 0, i32 1 ; #uses = 1	; i8**
    %subgep_ld7 = load i8** %getCloEnv.subgep6, align 4         ; #uses = 1	; i8*
    %getCloCode.subgep8 = getelementptr %3* %ptrfromnonptr1, i32 0, i32 0 ; #uses = 1	; void (i8*)**
    %subgep_ld9 = load void (i8*)** %getCloCode.subgep8, align 8 ; #uses = 1	; void (i8*)*
    tail call fastcc void %subgep_ld9(i8* %subgep_ld7)
    %loadStructParam = load %2* %autoload, align 4              ; #uses = 1	; { i1 (i8*)*, i8* }
    %loadStructParam12 = load %3* %ptrfromnonptr1, align 8      ; #uses = 1	; { void (i8*)*, i8* }
    %calltmp = tail call fastcc i32 @hof-until-case(%2 %loadStructParam, %3 %loadStructParam12) ; #uses = 0	; i32
    br label %case_end

  case_end:                                         ; preds = %entry, %casetest_0
    ret i32 0
  }

and finally this assembly (note that we don't enable tail recursion optimization for generated assembly)::

  hof_2D_until_2D_case:                   # @hof-until-case
  .Leh_func_begin8:
  # BB#0:                                 # %entry
          pushl	%ebp
  .Ltmp56:
          movl	%esp, %ebp
  .Ltmp57:
          pushl	%esi
          subl	$36, %esp
  .Ltmp58:
          movl	$0, -8(%ebp)
          movl	$0, -20(%ebp)
          movl	%edx, -28(%ebp)
          movl	%ecx, -32(%ebp)
          leal	-32(%ebp), %eax
          movl	%eax, -20(%ebp)
          movl	12(%ebp), %eax
          movl	%eax, -12(%ebp)
          movl	8(%ebp), %eax
          movl	%eax, -16(%ebp)
          leal	-16(%ebp), %eax
          movl	%eax, -8(%ebp)
          movl	-20(%ebp), %esi
          movl	4(%esi), %ecx
          calll	*(%esi)
  .Ltmp59:
          testb	$1, %al
          jne	.LBB8_2
  # BB#1:                                 # %casetest_0
          movl	-12(%ebp), %ecx
          calll	*-16(%ebp)
  .Ltmp60:
          movl	(%esi), %ecx
          movl	4(%esi), %edx
          movl	-16(%ebp), %eax
          movl	-12(%ebp), %esi
          movl	%esi, 4(%esp)
          movl	%eax, (%esp)
          calll	hof_2D_until_2D_case
  .Ltmp61:
  .LBB8_2:                                # %case_end
          xorl	%eax, %eax
          addl	$36, %esp
          popl	%esi
          popl	%ebp
          ret


Until as a language primitive
-----------------------------

Function ref-until source text::

   ref-until = {
     expect_i32 3;
     expect_i32 3;
     expect_i32 2;
     expect_i32 1;
     let r = (ref opaquely_i32 3);
      in print_i32 r^;
         until r^ == 0 then
           print_i32 r^;
           (r^ - 1) >^ r;
         end
     end
   };

Unoptimized::

  define fastcc void @ref-until() gc "fostergc" {
  entry:
    %stackref = alloca i32*                                     ; #uses = 3	; i32**
    call void @expect_i32(i32 3), !willnotgc !2
    call void @expect_i32(i32 3), !willnotgc !2
    call void @expect_i32(i32 2), !willnotgc !2
    call void @expect_i32(i32 1), !willnotgc !2
    %".x!11" = call i32 @opaquely_i32(i32 3)                    ; #uses = 1	; i32
    %mem = call i8* @memalloc_cell(%2* @__foster_typemap_gcatom) ; #uses = 1	; i8*
    %ptr = bitcast i8* %mem to i32*                             ; #uses = 1	; i32*
    %gcroot = bitcast i32** %stackref to i8**, !fostergcroot !0 ; #uses = 1	; i8**
    call void @llvm.gcroot(i8** %gcroot, i8* bitcast (%2* @__foster_typemap_gcatom to i8*))
    store i32* %ptr, i32** %stackref
    %"r!14" = load i32** %stackref                              ; #uses = 6	; i32*
    store i32 %".x!11", i32* %"r!14"
    %".x!12" = load i32* %"r!14"                                ; #uses = 1	; i32
    call void @print_i32(i32 %".x!12"), !willnotgc !2
    br label %until_test

  until_test:                                       ; preds = %until_body, %entry
    %".x!14" = load i32* %"r!14"                                ; #uses = 1	; i32
    %calltmp = tail call fastcc i1 @"primitive_==_i32"(i32 %".x!14", i32 0) ; #uses = 1	; i1
    br i1 %calltmp, label %until_cont, label %until_body

  until_body:                                       ; preds = %until_test
    %".x!16" = load i32* %"r!14"                                ; #uses = 1	; i32
    call void @print_i32(i32 %".x!16"), !willnotgc !2
    %".x!17" = load i32* %"r!14"                                ; #uses = 1	; i32
    %".x!19" = tail call fastcc i32 @primitive_-_i32(i32 %".x!17", i32 1) ; #uses = 1	; i32
    store i32 %".x!19", i32* %"r!14"
    br label %until_test

  until_cont:                                       ; preds = %until_test
    ret void
  }

Optimized (note that the loop test was duplicated and copied to the end of the loop)::

  define fastcc void @ref-until() gc "fostergc" {
  entry:
    %stackref = alloca i32*, align 4                            ; #uses = 2	; i32**
    %tmp.i = load %struct._IO_FILE** @stderr, align 4           ; #uses = 2	; { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, { \2, \4, i32 }*, \2, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }*
    %call.i.i = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %tmp.i, i8* getelementptr inbounds ([4 x i8]* @.str2, i32 0, i32 0), i32 3) ; #uses = 0	; i32
    %call3.i.i = call i32 @fflush(%struct._IO_FILE* %tmp.i)     ; #uses = 0	; i32
    %tmp.i1 = load %struct._IO_FILE** @stderr, align 4          ; #uses = 2	; { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, { \2, \4, i32 }*, \2, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }*
    %call.i.i2 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %tmp.i1, i8* getelementptr inbounds ([4 x i8]* @.str2, i32 0, i32 0), i32 3) ; #uses = 0	; i32
    %call3.i.i3 = call i32 @fflush(%struct._IO_FILE* %tmp.i1)   ; #uses = 0	; i32
    %tmp.i4 = load %struct._IO_FILE** @stderr, align 4          ; #uses = 2	; { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, { \2, \4, i32 }*, \2, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }*
    %call.i.i5 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %tmp.i4, i8* getelementptr inbounds ([4 x i8]* @.str2, i32 0, i32 0), i32 2) ; #uses = 0	; i32
    %call3.i.i6 = call i32 @fflush(%struct._IO_FILE* %tmp.i4)   ; #uses = 0	; i32
    %tmp.i7 = load %struct._IO_FILE** @stderr, align 4          ; #uses = 2	; { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, { \2, \4, i32 }*, \2, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }*
    %call.i.i8 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %tmp.i7, i8* getelementptr inbounds ([4 x i8]* @.str2, i32 0, i32 0), i32 1) ; #uses = 0	; i32
    %call3.i.i9 = call i32 @fflush(%struct._IO_FILE* %tmp.i7)   ; #uses = 0	; i32
    %".x!11" = call i32 @opaquely_i32(i32 3)                    ; #uses = 2	; i32
    %tmp.i10 = load %"class.foster::runtime::gc::copying_gc"** @_ZN6foster7runtime2gc9allocatorE, align 4 ; #uses = 1	; { { i8*, i8*, i8*, \4, i8* }*, { i8*, i8*, i8*, \4, i8* }*, i32, i32 }*
    %call.i = call i8* @_ZN6foster7runtime2gc10copying_gc13allocate_cellEPNS1_7typemapE(%"class.foster::runtime::gc::copying_gc"* %tmp.i10, %"struct.foster::runtime::gc::typemap"* @__foster_typemap_gcatom) ; #uses = 1	; i8*
    %ptr = bitcast i8* %call.i to i32*                          ; #uses = 5	; i32*
    %gcroot = bitcast i32** %stackref to i8**, !fostergcroot !0 ; #uses = 1	; i8**
    call void @llvm.gcroot(i8** %gcroot, i8* bitcast (%"struct.foster::runtime::gc::typemap"* @__foster_typemap_gcatom to i8*))
    store i32* %ptr, i32** %stackref, align 4
    store i32 %".x!11", i32* %ptr, align 4
    %tmp.i11 = load %struct._IO_FILE** @stdout, align 4         ; #uses = 2	; { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, { \2, \4, i32 }*, \2, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }*
    %call.i.i12 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %tmp.i11, i8* getelementptr inbounds ([4 x i8]* @.str2, i32 0, i32 0), i32 %".x!11") ; #uses = 0	; i32
    %call3.i.i13 = call i32 @fflush(%struct._IO_FILE* %tmp.i11) ; #uses = 0	; i32
    %".x!14.pr" = load i32* %ptr, align 4                       ; #uses = 2	; i32
    %eqtmp.i17 = icmp eq i32 %".x!14.pr", 0                     ; #uses = 1	; i1
    br i1 %eqtmp.i17, label %until_cont, label %until_body

  until_body:                                       ; preds = %entry, %until_body
    %".x!1418" = phi i32 [ %subtmp.i, %until_body ], [ %".x!14.pr", %entry ] ; #uses = 1	; i32
    %tmp.i14 = load %struct._IO_FILE** @stdout, align 4         ; #uses = 2	; { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, { \2, \4, i32 }*, \2, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }*
    %call.i.i15 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %tmp.i14, i8* getelementptr inbounds ([4 x i8]* @.str2, i32 0, i32 0), i32 %".x!1418") ; #uses = 0	; i32
    %call3.i.i16 = call i32 @fflush(%struct._IO_FILE* %tmp.i14) ; #uses = 0	; i32
    %".x!17" = load i32* %ptr, align 4                          ; #uses = 1	; i32
    %subtmp.i = add i32 %".x!17", -1                            ; #uses = 3	; i32
    store i32 %subtmp.i, i32* %ptr, align 4
    %eqtmp.i = icmp eq i32 %subtmp.i, 0                         ; #uses = 1	; i1
    br i1 %eqtmp.i, label %until_cont, label %until_body

  until_cont:                                       ; preds = %until_body, %entry
    ret void
  }

Assembly::

  ref_2D_until:                           # @ref-until
  .Leh_func_begin11:
  # BB#0:                                 # %entry
          pushl	%ebp
  .Ltmp80:
          movl	%esp, %ebp
  .Ltmp81:
          pushl	%ebx
          pushl	%edi
          pushl	%esi
          subl	$28, %esp
  .Ltmp82:
          movl	$0, -16(%ebp)
          movl	stderr, %esi
          movl	%esi, (%esp)
          movl	$3, 8(%esp)
          movl	$.L.str2, 4(%esp)
          calll	fprintf
  .Ltmp83:
          movl	%esi, (%esp)
          calll	fflush
  .Ltmp84:
          movl	stderr, %esi
          movl	%esi, (%esp)
          movl	$3, 8(%esp)
          movl	$.L.str2, 4(%esp)
          calll	fprintf
  .Ltmp85:
          movl	%esi, (%esp)
          calll	fflush
  .Ltmp86:
          movl	stderr, %esi
          movl	%esi, (%esp)
          movl	$2, 8(%esp)
          movl	$.L.str2, 4(%esp)
          calll	fprintf
  .Ltmp87:
          movl	%esi, (%esp)
          calll	fflush
  .Ltmp88:
          movl	stderr, %esi
          movl	%esi, (%esp)
          movl	$1, 8(%esp)
          movl	$.L.str2, 4(%esp)
          calll	fprintf
  .Ltmp89:
          movl	%esi, (%esp)
          calll	fflush
  .Ltmp90:
          movl	$3, (%esp)
          calll	opaquely_i32
  .Ltmp91:
          movl	%eax, %esi
          movl	_ZN6foster7runtime2gc9allocatorE, %eax
          movl	%eax, (%esp)
          movl	$__foster_typemap_gcatom, 4(%esp)
          calll	_ZN6foster7runtime2gc10copying_gc13allocate_cellEPNS1_7typemapE
  .Ltmp92:
          movl	%eax, %edi
          movl	%edi, -16(%ebp)
          movl	%esi, (%edi)
          movl	stdout, %ebx
          movl	%esi, 8(%esp)
          movl	%ebx, (%esp)
          movl	$.L.str2, 4(%esp)
          calll	fprintf
  .Ltmp93:
          movl	%ebx, (%esp)
          calll	fflush
  .Ltmp94:
          movl	(%edi), %eax
          jmp	.LBB11_2
          .align	16, 0x90
  .LBB11_1:                               # %until_body
                                          #   in Loop: Header=BB11_2 Depth=1
          movl	stdout, %esi
          movl	%eax, 8(%esp)
          movl	%esi, (%esp)
          movl	$.L.str2, 4(%esp)
          calll	fprintf
  .Ltmp95:
          movl	%esi, (%esp)
          calll	fflush
  .Ltmp96:
          movl	(%edi), %eax
          decl	%eax
          movl	%eax, (%edi)
  .LBB11_2:                               # %until_body
                                          # =>This Inner Loop Header: Depth=1
          testl	%eax, %eax
          jne	.LBB11_1
  # BB#3:                                 # %until_cont
          addl	$28, %esp
          popl	%esi
          popl	%edi
          popl	%ebx
          popl	%ebp
          ret

