cond v                    lookupWith { p => p v }        
  of p1 -> e1                        [ (s1, { e1 } )     
  of p2 -> e2                        , (s2, { e2 } )
  ...                                ...            
 end                                 ] !            
                                                    
       v :: T
p1 .. pn :: T -> Bool

e.g.

cond "foo"                 lookupWith { re => re.matches("foo") }
  of /bar/ -> ...                     [ ( /bar/ , { ... } )
 end                                  , ]

 where /bar/ :: Text -> Bool
                              
cond v                       lookupWith { s => s ! == v }
  of s1 -> e1                           [ ( { s1 } , { e1 } )
  of s2 -> e2                           , ( { s2 } , { e2 } )                                         
  ...                                   ...            
 end                                    ] !                                         
                                                                                                        
v :: T
s1 :: T
s2 :: T


cond, case

