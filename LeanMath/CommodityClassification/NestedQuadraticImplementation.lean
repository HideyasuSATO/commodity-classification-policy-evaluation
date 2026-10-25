module

public import LeanMath.CommodityClassification.NestedPreferenceOptimality
public import LeanMath.CommodityClassification.CommonBenchmarkUtility

/-! A concrete utility-generated local demand for every SPD outer response. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix Equilibrium Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : DemandNests.Data n g)

def quadraticOuter (DG : Mat g g) : Vec g → Vec g :=
  affineDemand (fun _ => 1) (d.partition.sales d.p d.q) DG

def outerUtility (DG : Mat g g) (c : ℝ) : Vec g → ℝ :=
  benchmarkUtility (fun _ => 1) (d.partition.sales d.p d.q) DG c

theorem quadraticOuter_benchmark (DG : Mat g g) :
    d.quadraticOuter DG (fun _ => 1)=d.partition.sales d.p d.q :=
  affineDemand_base _ _ _

theorem quadraticOuter_derivative (DG : Mat g g) :
    HasFDerivAt (d.quadraticOuter DG) (-matCLM DG) (fun _ => 1) :=
  affineDemand_derivative _ _ _

theorem quadratic_nested_benchmark (DG : Mat g g) :
    d.demand (d.quadraticOuter DG) d.p=d.q :=
  d.demand_benchmark _ (d.quadraticOuter_benchmark DG)

theorem quadratic_nested_derivative (DG : Mat g g) :
    HasFDerivAt (d.demand (d.quadraticOuter DG)) (-matCLM (d.demandMatrix DG)) d.p :=
  d.demand_actual_matrix_derivative _ DG (d.quadraticOuter_benchmark DG)
    (d.quadraticOuter_derivative DG)

theorem quadraticOuter_optimal (DG : Mat g g) (hDG : DG.PosDef) (c : ℝ) (P Z : Vec g) :
    d.outerUtility DG c Z-dotProduct P Z ≤
      d.outerUtility DG c (d.quadraticOuter DG P)-dotProduct P (d.quadraticOuter DG P) :=
  benchmarkUtility_surplus_maximum _ _ P Z DG hDG c

theorem quadratic_nested_positive_near (DG : Mat g g) :
    ∀ᶠ r in 𝓝 d.p, (∀i,0<r i) ∧ ∀a,0<d.quadraticOuter DG (d.priceMap r) a := by
  have hc := (d.quadraticOuter_derivative DG).continuousAt
  rw [←d.priceMap_benchmark] at hc
  have ht := hc.comp d.priceMap_hasFDerivAt.continuousAt
  have hbase : d.quadraticOuter DG (d.priceMap d.p)∈CESCost.PositivePrices g := by
    rw [d.priceMap_benchmark,d.quadraticOuter_benchmark]
    exact d.partition.sales_pos d.p d.q d.hp d.hq
  have hy : ∀ᶠ r in 𝓝 d.p, d.quadraticOuter DG (d.priceMap r)∈CESCost.PositivePrices g :=
    ht (CESCost.positivePrices_open.mem_nhds hbase)
  have hr : ∀ᶠ r in 𝓝 d.p, r∈CESCost.PositivePrices n :=
    CESCost.positivePrices_open.mem_nhds d.hp
  exact hr.and hy

theorem quadratic_nested_optimal_near (DG : Mat g g) (hDG : DG.PosDef) (c : ℝ) :
    ∀ᶠ r in 𝓝 d.p, (∀i,0<r i) ∧ (∀i,0<d.demand (d.quadraticOuter DG) r i) ∧
      IsMaxOn (fun x => d.outerUtility DG c (d.quantityMap x)-dotProduct r x)
        {x | ∀i,0≤x i} (d.demand (d.quadraticOuter DG) r) := by
  filter_upwards [d.quadratic_nested_positive_near DG] with r hr
  have h := d.actual_demand_optimal hr.1 (d.quadraticOuter DG) (d.outerUtility DG c)
    Set.univ hr.2 (Set.mem_univ _) (fun Z _ => d.quadraticOuter_optimal DG hDG c _ Z)
  refine ⟨hr.1,h.1,?_⟩
  simpa only [Set.mem_univ,and_true] using h.2.2

theorem outerUtility_marginals_positive_near (DG : Mat g g) :
    ∀ᶠ Y in 𝓝 (d.partition.sales d.p d.q), (∀a,0<Y a) ∧
      ∀a,0<benchmarkGradient (fun _ => 1) (d.partition.sales d.p d.q) DG Y a :=
  benchmarkUtility_marginals_positive_near _ _ DG (fun _ => zero_lt_one)
    (d.partition.sales_pos d.p d.q d.hp d.hq)

end CommodityClassification.DemandNests.Data
