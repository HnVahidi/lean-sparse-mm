module

public import SparseMM.Main
public import SparseMM.BroadcastLower

@[expose] public section

/-! Constructor signatures make the public model fields part of the
independent statement comparison. These definitions add no assumptions. -/

namespace SparseMM.Signatures

def StaticPlan_constructor := @Model.StaticPlan.mk
def Stage_constructor := @LocalPipeline.Stage.mk
def Program_constructor := @LocalPipeline.Program.mk
def Clustering_constructor := @Clustering.mk
def BroadcastSystem_constructor := @BroadcastLower.System.mk

end SparseMM.Signatures
