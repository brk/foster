Lowering Foster IL to LLVM
==========================

Primitive Linking Language
==========================

Skeleton::

        name = readLLVMModuleFromPath(llvm-module-path);
        type = name->getTypeByName(typename);
        type = getPointerTo(type)
        addTypeName(name, type)

        ?? ParsingContext::insertType(name, PrimitiveTypeAST::get(name, type));

        getEmptyStructType()

        var = name->getNamedGlobal("name");
        module->getOrInsertGlobal("name", getContainedType(var))

        addStandardExternDeclarations()
        addCoroTransferDeclarations()

        putModuleMembersInScope
        putModuleMembersInInternalScope

        codegen

        cleanup

        dump prelinked to file

        run warning passes

        linkTo(other_module_bc, name, module);

        dump postlinked to file

        dump module to bitcode

        print statistics
