module

public import LeanMath.CommodityClassification.SymmetricDemandCoordinates

/-! Determinant-cleared gain differences as actual multivariate polynomials. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer
variable {n a b : ℕ}

def polynomialConstantMatrix (M : Mat a b) :
    Matrix (Fin a) (Fin b) (MvPolynomial (SymmetricEntry n) ℝ) := M.map MvPolynomial.C

theorem polynomialConstantMatrix_eval (x : SymmetricEntry n → ℝ) (M : Mat a b) :
    (polynomialConstantMatrix M).map (MvPolynomial.eval x)=M := by
  ext i j
  simp [polynomialConstantMatrix]

theorem ringHom_comp_mulVec {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Matrix (Fin a) (Fin b) R) (v : Fin b → R) :
    φ ∘ (M *ᵥ v)=M.map φ *ᵥ (φ ∘ v) := by
  funext i
  exact φ.map_mulVec M v i

end CommodityClassification.Genericity

namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

def gainKPolynomial (C : Mat n k) : Matrix (Fin k) (Fin k) (MvPolynomial (SymmetricEntry n) ℝ) :=
  polynomialConstantMatrix C.transpose*symbolicDemand n*polynomialConstantMatrix C+
    polynomialConstantMatrix (F.supplyT C)

def gainLoadPolynomial (C : Mat n k) : Fin k → MvPolynomial (SymmetricEntry n) ℝ :=
  polynomialConstantMatrix C.transpose *ᵥ
    (symbolicDemand n *ᵥ (fun i => MvPolynomial.C (F.b i)))

def gainNumeratorPolynomial (C : Mat n k) : MvPolynomial (SymmetricEntry n) ℝ :=
  dotProduct (F.gainLoadPolynomial C) ((F.gainKPolynomial C).adjugate *ᵥ F.gainLoadPolynomial C)

def gainDifferencePolynomial (C1 C0 : Mat n k) : MvPolynomial (SymmetricEntry n) ℝ :=
  F.gainNumeratorPolynomial C1*(F.gainKPolynomial C0).det-
    F.gainNumeratorPolynomial C0*(F.gainKPolynomial C1).det

theorem gainKPolynomial_eval (D : SymmetricDemand n) (C : Mat n k) :
    (F.gainKPolynomial C).map (MvPolynomial.eval (symmetricCoordinates D))=
      Regularity.K F.p F.q D.val F.fixedR F.sigma C := by
  let φ := MvPolynomial.eval (symmetricCoordinates D)
  rw [gainKPolynomial,Matrix.map_add _ φ.map_add,Matrix.map_mul,Matrix.map_mul,
    polynomialConstantMatrix_eval,symbolicDemand_evaluated,polynomialConstantMatrix_eval,
    polynomialConstantMatrix_eval,Regularity.K_eq_demand_add_substitution]
  rfl

theorem gainLoadPolynomial_eval (D : SymmetricDemand n) (C : Mat n k) :
    MvPolynomial.eval (symmetricCoordinates D) ∘ F.gainLoadPolynomial C=
      C.transpose *ᵥ (D.val *ᵥ F.b) := by
  let φ := MvPolynomial.eval (symmetricCoordinates D)
  have hb : φ ∘ (fun i => MvPolynomial.C (F.b i))=F.b := by
    funext i
    exact MvPolynomial.eval_C _
  rw [gainLoadPolynomial,ringHom_comp_mulVec,ringHom_comp_mulVec,
    polynomialConstantMatrix_eval,symbolicDemand_evaluated,hb]

theorem gainNumeratorPolynomial_eval (D : SymmetricDemand n) (C : Mat n k) :
    MvPolynomial.eval (symmetricCoordinates D) (F.gainNumeratorPolynomial C)=
      dotProduct (C.transpose *ᵥ (D.val *ᵥ F.b))
        ((Regularity.K F.p F.q D.val F.fixedR F.sigma C).adjugate *ᵥ
          (C.transpose *ᵥ (D.val *ᵥ F.b))) := by
  let φ := MvPolynomial.eval (symmetricCoordinates D)
  have ha : (F.gainKPolynomial C).adjugate.map φ=
      (Regularity.K F.p F.q D.val F.fixedR F.sigma C).adjugate := by
    rw [←RingHom.mapMatrix_apply,φ.map_adjugate, RingHom.mapMatrix_apply,F.gainKPolynomial_eval D C]
  rw [gainNumeratorPolynomial,φ.map_dotProduct,ringHom_comp_mulVec,ha,
    F.gainLoadPolynomial_eval]

theorem gainDeterminantPolynomial_eval (D : SymmetricDemand n) (C : Mat n k) :
    MvPolynomial.eval (symmetricCoordinates D) (F.gainKPolynomial C).det=
      (Regularity.K F.p F.q D.val F.fixedR F.sigma C).det := by
  rw [RingHom.map_det,RingHom.mapMatrix_apply,F.gainKPolynomial_eval]

theorem demandGain_adjugate (D : Mat n n) (C : Mat n k) :
    F.demandGain D C=
      dotProduct (C.transpose *ᵥ (D *ᵥ F.b))
        ((Regularity.K F.p F.q D F.fixedR F.sigma C).adjugate *ᵥ (C.transpose *ᵥ (D *ᵥ F.b)))/
      (Regularity.K F.p F.q D F.fixedR F.sigma C).det := by
  simp only [demandGain,Matrix.inv_def,Ring.inverse_eq_inv,smul_mulVec,dotProduct_smul,smul_eq_mul]
  ring

theorem gainDifferencePolynomial_eval (D : SymmetricDemand n) (C1 C0 : Mat n k)
    (h1 : (Regularity.K F.p F.q D.val F.fixedR F.sigma C1).det≠0)
    (h0 : (Regularity.K F.p F.q D.val F.fixedR F.sigma C0).det≠0) :
    MvPolynomial.eval (symmetricCoordinates D) (F.gainDifferencePolynomial C1 C0)=
      (Regularity.K F.p F.q D.val F.fixedR F.sigma C1).det*
      (Regularity.K F.p F.q D.val F.fixedR F.sigma C0).det*
      (F.demandGain D.val C1-F.demandGain D.val C0) := by
  simp only [gainDifferencePolynomial,map_sub,map_mul,F.gainNumeratorPolynomial_eval,
    F.gainDeterminantPolynomial_eval,F.demandGain_adjugate]
  field_simp

end CommodityClassification.Equilibrium.BenchmarkFamily
