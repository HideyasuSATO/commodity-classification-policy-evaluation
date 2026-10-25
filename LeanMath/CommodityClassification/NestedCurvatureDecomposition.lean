module

public import LeanMath.CommodityClassification.NestedDemandMatrix

/-! Aggregate-price and within-nest components of the actual demand curvature. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem sum_by_nest (f : Vec n) : (∑a,∑i∈d.partition.cell a,f i)=∑i,f i := by
  simp only [Partition.cell,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sum_nest_multiplier (f : Vec n) (v : Vec g) :
    (∑i,f i*v (d.partition.group i))=∑a,(∑i∈d.partition.cell a,f i)*v a := by
  symm
  simp only [Partition.cell,Finset.sum_filter,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem cell_price_sum (h : Vec n) (a : Fin g) :
    (∑i∈d.partition.cell a,d.q i*h i)=d.partition.sales d.p d.q a*d.priceDerivative h a := by
  rw [d.priceDerivative_apply]
  field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq a).ne']

def withinCurvature (h : Vec n) (a : Fin g) : ℝ :=
  dotProduct (d.restrict a h)
    (Supply.curvature (d.nest a).expenditureData.a (d.nest a).expenditureData.w0
      (d.nest a).expenditureData.p *ᵥ d.restrict a h)

theorem withinCurvature_nonneg (h : Vec n) (a : Fin g) : 0≤d.withinCurvature h a :=
  Supply.curvature_nonneg (d.nest a).expenditureData (d.restrict a h)

theorem withinCurvature_quad (h : Vec n) (a : Fin g) :
    d.partition.sales d.p d.q a*d.withinCurvature h a=
      (∑i∈d.partition.cell a,(d.q i/d.p i)*(h i)^2)-
      d.partition.sales d.p d.q a*(d.priceDerivative h a)^2 := by
  unfold withinCurvature
  rw [Supply.curvature_quad]
  have hp : dotProduct (d.nest a).expenditureData.a (d.restrict a h)=d.priceDerivative h a := by
    exact (CESCost.weightedLinear_apply _ _).symm
  rw [hp]
  change d.partition.sales d.p d.q a*((∑j,(d.q (d.product a j)/(d.nest a).sales/
    d.p (d.product a j))*(h (d.product a j))^2)-(d.priceDerivative h a)^2/1)=_
  rw [d.nest_sales]
  have hs : (∑j,(d.q (d.product a j)/d.partition.sales d.p d.q a/d.p (d.product a j))*
      (h (d.product a j))^2)=
      (∑i∈d.partition.cell a,(d.q i/d.p i)*(h i)^2)/d.partition.sales d.p d.q a := by
    rw [←d.sum_restrict a (fun i => (d.q i/d.p i)*(h i)^2),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq a).ne']

theorem quadratic_diagonal_part (DG : Matrix (Fin g) (Fin g) ℝ) (h : Vec n) :
    dotProduct h (d.demandMatrix DG *ᵥ h)=
      (∑i,d.eta (d.partition.group i)*(d.q i/d.p i)*(h i)^2)+
      dotProduct (d.priceDerivative h) (DG *ᵥ d.priceDerivative h)-
      ∑a,d.eta a*d.partition.sales d.p d.q a*(d.priceDerivative h a)^2 := by
  change (∑i,h i*(d.demandMatrix DG *ᵥ h) i)=_
  simp_rw [d.demandMatrix_apply]
  have he : (∑i,h i*(d.eta (d.partition.group i)*(d.q i/d.p i)*h i+
      (d.q i/d.partition.sales d.p d.q (d.partition.group i))*
        (DG *ᵥ d.priceDerivative h) (d.partition.group i)-
      d.eta (d.partition.group i)*d.q i*d.priceDerivative h (d.partition.group i)))=
      (∑i,d.eta (d.partition.group i)*(d.q i/d.p i)*(h i)^2)+
      (∑i,(d.q i*h i)*((DG *ᵥ d.priceDerivative h) (d.partition.group i)/
        d.partition.sales d.p d.q (d.partition.group i)))-
      ∑i,(d.q i*h i)*(d.eta (d.partition.group i)*d.priceDerivative h (d.partition.group i)) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,d.sum_nest_multiplier (fun i => d.q i*h i)
    (fun a => (DG *ᵥ d.priceDerivative h) a/d.partition.sales d.p d.q a),
    d.sum_nest_multiplier (fun i => d.q i*h i) (fun a => d.eta a*d.priceDerivative h a)]
  simp_rw [d.cell_price_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq a).ne']
  · apply Finset.sum_congr rfl
    intro a _
    ring

theorem demand_quadratic_decomposition (DG : Matrix (Fin g) (Fin g) ℝ) (h : Vec n) :
    dotProduct h (d.demandMatrix DG *ᵥ h)=
      (∑a,d.eta a*d.partition.sales d.p d.q a*d.withinCurvature h a)+
      dotProduct (d.priceDerivative h) (DG *ᵥ d.priceDerivative h) := by
  have hs : (∑a,d.eta a*d.partition.sales d.p d.q a*d.withinCurvature h a)=
      (∑i,d.eta (d.partition.group i)*(d.q i/d.p i)*(h i)^2)-
      ∑a,d.eta a*d.partition.sales d.p d.q a*(d.priceDerivative h a)^2 := by
    simp_rw [mul_assoc (d.eta _),d.withinCurvature_quad,mul_sub,Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [←d.sum_by_nest (fun i => d.eta (d.partition.group i)*((d.q i/d.p i)*(h i)^2))]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(d.partition.mem_cell a i).mp hi]
  rw [d.quadratic_diagonal_part,hs]
  ring

end CommodityClassification.DemandNests.Data
