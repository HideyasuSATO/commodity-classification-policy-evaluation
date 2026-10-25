module

public import LeanMath.CommodityClassification.NestedCurvatureDecomposition

/-! Strict positive definiteness from within-nest and outer curvature. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem outerAdjustment_symmetric (DG : Matrix (Fin g) (Fin g) ℝ) (hDG : DG.IsSymm) :
    (d.outerAdjustment DG).IsSymm := by
  change (d.outerAdjustment DG).transpose=d.outerAdjustment DG
  simp only [outerAdjustment,transpose_mul,transpose_sub,diagonal_transpose,hDG.eq,Matrix.mul_assoc]

theorem demandMatrix_symmetric (DG : Matrix (Fin g) (Fin g) ℝ) (hDG : DG.IsSymm) :
    (d.demandMatrix DG).IsSymm := by
  change (d.demandMatrix DG).transpose=d.demandMatrix DG
  have hd : (diagonal (fun i => d.eta (d.partition.group i))*Supply.xi d.p d.q).transpose=
      diagonal (fun i => d.eta (d.partition.group i))*Supply.xi d.p d.q := by
    simp only [Supply.xi,diagonal_mul_diagonal,diagonal_transpose]
  rw [demandMatrix,transpose_add,hd,transpose_mul,transpose_mul,transpose_transpose,
    (d.outerAdjustment_symmetric DG hDG).eq]
  simp only [Matrix.mul_assoc]

theorem withinCurvature_zero_price_zero (h : Vec n) (a : Fin g)
    (hw : d.withinCurvature h a=0) (hy : d.priceDerivative h a=0) : d.restrict a h=0 := by
  obtain ⟨t,ht⟩ := (Supply.curvature_zero_iff (d.nest a).expenditureData (d.restrict a h)).mp hw
  have hp : d.priceDerivative h a=t := by
    change CESCost.weightedLinear (d.nest a).expenditureData.a (d.restrict a h)=t
    rw [ht,map_smul,CESCost.weightedLinear_apply,(d.nest a).expenditureData.cost_identity]
    change t*1=t
    ring
  have ht0 : t=0 := hp.symm.trans hy
  rw [ht,ht0,zero_smul]

theorem zero_price_and_curvature_direction (h : Vec n) (hy : d.priceDerivative h=0)
    (hw : ∀a,d.withinCurvature h a=0) : h=0 := by
  funext i
  have hh := d.withinCurvature_zero_price_zero h (d.partition.group i)
    (hw _) (congrFun hy _)
  have hi := congrFun hh (d.localIndex i)
  simpa only [d.restrict_apply,d.product_localIndex,Pi.zero_apply] using hi

theorem sum_withinCurvature_nonneg (h : Vec n) :
    0≤∑a,d.eta a*d.partition.sales d.p d.q a*d.withinCurvature h a :=
  Finset.sum_nonneg (fun a _ => mul_nonneg
    (mul_pos (d.heta a) (d.partition.sales_pos d.p d.q d.hp d.hq a)).le
    (d.withinCurvature_nonneg h a))

theorem sum_withinCurvature_pos_of_zero_price (h : Vec n) (hh : h≠0)
    (hy : d.priceDerivative h=0) :
    0<∑a,d.eta a*d.partition.sales d.p d.q a*d.withinCurvature h a := by
  have hn : ¬∀a,d.withinCurvature h a=0 := fun hw => hh (d.zero_price_and_curvature_direction h hy hw)
  obtain ⟨a,ha⟩ := not_forall.mp hn
  have hterm : 0<d.eta a*d.partition.sales d.p d.q a*d.withinCurvature h a :=
    mul_pos (mul_pos (d.heta a) (d.partition.sales_pos d.p d.q d.hp d.hq a))
      (lt_of_le_of_ne (d.withinCurvature_nonneg h a) (fun hz => ha hz.symm))
  apply lt_of_lt_of_le hterm
  exact Finset.single_le_sum (fun b _ => mul_nonneg
    (mul_pos (d.heta b) (d.partition.sales_pos d.p d.q d.hp d.hq b)).le
    (d.withinCurvature_nonneg h b)) (Finset.mem_univ a)

theorem demandMatrix_posDef (DG : Matrix (Fin g) (Fin g) ℝ) (hDG : DG.PosDef) :
    (d.demandMatrix DG).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · simpa only [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial] using
      (d.demandMatrix_symmetric DG hDG.isHermitian.isSymm).eq
  · intro h hh
    simp only [star_trivial]
    rw [d.demand_quadratic_decomposition]
    by_cases hy : d.priceDerivative h=0
    · rw [hy,Matrix.mulVec_zero,dotProduct_zero,add_zero]
      exact d.sum_withinCurvature_pos_of_zero_price h hh hy
    · have hp : 0<dotProduct (d.priceDerivative h) (DG *ᵥ d.priceDerivative h) := by
        simpa only [star_trivial] using hDG.dotProduct_mulVec_pos hy
      exact add_pos_of_nonneg_of_pos (d.sum_withinCurvature_nonneg h) hp

end CommodityClassification.DemandNests.Data
