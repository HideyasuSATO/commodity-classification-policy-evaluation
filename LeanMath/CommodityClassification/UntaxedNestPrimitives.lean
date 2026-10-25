module

public import LeanMath.CommodityClassification.NestedOriginalUtilityWitness
public import LeanMath.CommodityClassification.SeparableFourMoments

/-! Exact primitives of the four-good untaxed-nest example. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

def prices : Vec 4 := fun _ => 1
def quantities : Vec 4 := fun _ => 1/4
def policy : Vec 4 := ![1,1,0,0]
def eta : Vec 2 := ![1,2]
def beta : Vec 2 := ![1,0]
def outerD : Mat 2 2 := diagonal (fun _ => 1/2)
def demand : Mat 4 4 := ![![1/4,0,0,0],![0,1/4,0,0],![0,0,3/8,-1/8],![0,0,-1/8,3/8]]
def parent : Partition 4 1 := SeparableFour.parent
def nests : Partition 4 2 := SeparableFour.fine
def coordinates (t : ℝ) : Mat 4 1 := ![![1/4],![1/4],![-1/4+t],![-1/4-t]]
def inputs (t : ℝ) : Mat 4 2 := fun i j =>
  if j=0 then (1+coordinates t i 0)/2 else (1-coordinates t i 0)/2

theorem eta_pos : ∀a,0<eta a := by intro a;fin_cases a <;> norm_num [eta]

def nestData : DemandNests.Data 4 2 :=
  ⟨nests,prices,quantities,eta,(by intro i;norm_num [prices]),
    (by intro i;norm_num [quantities]),eta_pos⟩

theorem nest_sales : nests.sales prices quantities=![1/2,1/2] := by
  ext a;fin_cases a <;>
    norm_num [Partition.sales,Partition.Q,nests,SeparableFour.fine,prices,quantities,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem outerD_posDef : outerD.PosDef := Matrix.PosDef.diagonal (fun _ => by norm_num)

theorem demand_eq_nested : demand=nestData.demandMatrix outerD := by
  have hs : nestData.partition.sales nestData.p nestData.q=![1/2,1/2] := nest_sales
  unfold DemandNests.Data.demandMatrix DemandNests.Data.outerAdjustment
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [demand,nestData,outerD,eta,nests,SeparableFour.fine,prices,quantities,
      Supply.xi,Partition.Q,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ]

theorem demand_posDef : demand.PosDef := by
  rw [demand_eq_nested]
  exact nestData.demandMatrix_posDef outerD outerD_posDef

theorem policy_eq_nested : policy=nestData.proportionalPolicy beta := by
  ext i;fin_cases i <;>
    norm_num [policy,DemandNests.Data.proportionalPolicy,nestData,nests,SeparableFour.fine,
      prices,beta,Partition.Q,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem reconstruct_inputs (t : ℝ) :
    Supply.Example.frame.reconstruct prices (coordinates t)=inputs t := by
  have hw : inputs t *ᵥ Supply.Example.frame.w=prices := by
    ext i
    simp [inputs,Supply.Example.frame,prices,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  have hv : inputs t*Supply.Example.frame.V=coordinates t := by
    ext i j;fin_cases j
    change (∑r : Fin 2,inputs t i r*Supply.Example.frame.V r 0)=coordinates t i 0
    simp [inputs,Supply.Example.frame,Fin.sum_univ_succ]
    ring
  rw [←hw,←hv]
  exact Supply.Example.frame.reconstruct_original (inputs t)

theorem parent_report (t : ℝ) : parent.report quantities (coordinates t)=0 := by
  ext i j;fin_cases i;fin_cases j
  change (∑l : Fin 4,quantities l*coordinates t l 0)=0
  norm_num [quantities,coordinates,Fin.sum_univ_succ]
  ring

theorem nest_report (t : ℝ) : nests.report quantities (coordinates t)=![![1/8],![-1/8]] := by
  ext i j
  change (∑l : Fin 4,(if nests.group l=i then quantities l else 0)*coordinates t l j)=_
  fin_cases i <;> fin_cases j <;>
    norm_num [nests,SeparableFour.fine,quantities,coordinates,Fin.sum_univ_succ]
  ring

theorem factor_share_lower (t : ℝ) (ht : |t|≤1/4) : ∀i j,(1/4 : ℝ) ≤ inputs t i j := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp ht
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [inputs,coordinates] <;> linarith

theorem coordinates_candidate (t : ℝ) (ht : |t|≤1/4) :
    coordinates t∈Supply.Example.frame.Candidates prices quantities parent 0 := by
  refine ⟨?_,parent_report t⟩
  change Positive (Supply.Example.frame.reconstruct prices (coordinates t))
  rw [reconstruct_inputs]
  intro i j
  exact lt_of_lt_of_le (by norm_num) (factor_share_lower t ht i j)

def family : Equilibrium.BenchmarkFamily 4 1 1 where
  frame := Supply.Example.frame
  p := prices
  q := quantities
  b := policy
  D := demand
  sigma := 1
  parents := parent
  report := 0
  reference := coordinates 0
  reference_mem := coordinates_candidate 0 (by norm_num)
  hp := by intro i;norm_num [prices]
  hq := by intro i;norm_num [quantities]
  hw := by intro j;fin_cases j <;> norm_num [Supply.Example.frame]
  ha0 := by intro j;fin_cases j <;> norm_num [Supply.Example.frame]
  hD := demand_posDef
  hsigma := by norm_num

def candidate (t : ℝ) (ht : |t|≤1/4) : family.Candidate := ⟨coordinates t,coordinates_candidate t ht⟩

theorem fixed_R : family.fixedR=![![1]] := by
  change Supply.knownR Supply.Example.frame.w Supply.Example.frame.V
    (Supply.totalInputs quantities (Supply.Example.frame.reconstruct prices (coordinates 0)))=_
  rw [reconstruct_inputs]
  have hi : Supply.totalInputs quantities (inputs 0)=![1/2,1/2] := by
    ext j;fin_cases j <;> norm_num [Supply.totalInputs,inputs,coordinates,quantities,Fin.sum_univ_succ]
  rw [hi]
  ext i j;fin_cases i;fin_cases j
  change (∑r : Fin 2,(∑s : Fin 2,Supply.Example.frame.V s 0 *
    (diagonal (fun k : Fin 2 => ![1/2,1/2] k / Supply.Example.frame.w k)) s r)*
      Supply.Example.frame.V r 0)=1
  norm_num [Supply.Example.frame,Matrix.diagonal,Fin.sum_univ_succ]

end CommodityClassification.UntaxedNest
