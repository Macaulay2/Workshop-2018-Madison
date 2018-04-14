-*
restart
loadPackage("VirtualResolutions", Reload =>true)
installPackage "VirtualResolutions"
viewHelp "VirtualResolutions"
viewHelp "TateOnProducts"
check "VirtualResolutions"
*-

newPackage ("VirtualResolutions",
Version => "0.0",
Date => "April 14, 2018",
Headline => "Methods for virtual resolutions on products of projective spaces",
Authors =>{
    {Name =>"David Eisenbud"}, 
    {Name => "Christine Berkesch"}
    },
PackageExports => {"TateOnProducts"},
DebuggingMode => true
)

export{}


--------------------------
-- Begining of the documentation
------------------------
beginDocumentation()



--------------------------
-- Begining of the TESTS
------------------------


end--