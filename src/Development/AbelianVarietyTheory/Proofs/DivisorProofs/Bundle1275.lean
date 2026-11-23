module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinors
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowKillDelta

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.FockKill
open scoped Real Classical

section Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp}

theorem exists_coef_any {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ)) :
    ∃ ν : Fin T.rank → Fin T.rank → ℂ, (∀ a b : Fin T.rank, ¬ (p ≤ (a : ℕ) ∧ (b : ℕ) < p) → ν a b = 0) ∧
      ∀ a c b d, ∀ u, u = unitMap (BS τ) (BT τ) a c → ∀ u', u' = unitMap (BS τ) (BT τ) b d →
        ((omDir S T τ (X * u) τ u' : ℝ) + Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * u)) τ u' : ℝ)) +
          (-Complex.I) * ((omDir S T τ (X * cplxO 1 (cart M τ) u) τ u' : ℝ) +
            Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * cplxO 1 (cart M τ) u)) τ u' : ℝ)) =
        (if c = d then ν a b else 0) + (if d = c then ν b a else 0) := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨ε, hε, -, ht⟩ := hBT
  let o : Matrix (Fin T.rank) (Fin T.rank) ℂ → Fin T.rank → Fin T.rank → ℝ := fun W a b =>
    2 * (tauE D τ D.host.xi0 * ((BT τ)ᴴ * gramAt D T τ * W * BT τ) a b).re
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have osym : ∀ W ∈ lieAt T τ, ∀ a b, o W a b = o W b a := fun W hW a b =>
    congrArg (2 * ·) (skew_entry (GlobalTheory.SmoothAutCheck.gramAt_herm T τ) hW hre a b)
  have ozero : ∀ W, cart M τ * W = -(W * cart M τ) → ∀ a b : Fin T.rank, ((a : ℕ) < p ↔ (b : ℕ) < p) →
      o W a b = 0 := fun W hW a b hab => by
    simp only [o]
    rw [zero_entry (hT τ) ht hW, mul_zero, Complex.zero_re, mul_zero]
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hε b with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp only [h1, h3]
    · norm_num
    · exact absurd (hab.1 h2) (by omega)
    · exact absurd (hab.2 h4) (by omega)
    · norm_num
  have hom1 : ∀ W a c b d, omDir S T τ (W * unitMap (BS τ) (BT τ) a c) τ (unitMap (BS τ) (BT τ) b d) =
      if c = d then o W b a else 0 := fun W a c b d => by
    rw [omDir, if_pos rfl, trace_unitMap (hB τ)]
    split_ifs <;> simp [o]
  have hJ : ∀ (W : Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      cplxO 1 (cart M τ) (W * u) = Complex.I • (cart M τ * W) * u := fun W u => by
    rw [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  have hJ' : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      X * cplxO 1 (cart M τ) u = (-(Complex.I • (cart M τ * X))) * u := fun u => by
    rw [cplxO, Matrix.mul_one, ha, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hJ'' : Complex.I • (cart M τ * -(Complex.I • (cart M τ * X))) = X := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, (hT τ).1, Matrix.one_mul, smul_neg, smul_smul,
      Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  have oneg : ∀ W a b, o (-W) a b = -o W a b := fun W a b => by
    simp only [o, Matrix.neg_mul, Matrix.neg_apply, mul_neg, Complex.neg_re]
  clear_value o
  refine ⟨fun a b => if p ≤ (a : ℕ) ∧ (b : ℕ) < p then
    2 * (o X a b + Complex.I * o (Complex.I • (cart M τ * X)) a b) else 0, fun a b h => if_neg h, ?_⟩
  rintro a c b d _ rfl _ rfl
  rw [hJ', hJ, hJ, hJ'', hom1, hom1, hom1, oneg]
  by_cases e3 : c = d
  swap
  · simp [e3, Ne.symm e3]
  subst e3
  simp only [if_true]
  have z1 := ozero _ ha
  have z2 := ozero _ (anti_I ha)
  have s1 := osym _ lX a b
  have s2 := osym _ lY a b
  generalize Complex.I • (cart M τ * X) = Y at z2 s2
  rw [s1, s2]
  have e : (o X b a : ℂ) + Complex.I * o Y b a + -Complex.I * ((-o Y b a : ℝ) + Complex.I * o X b a) =
      2 * (o X b a + Complex.I * o Y b a) := by
    push_cast
    linear_combination (-o X b a : ℂ) * Complex.I_mul_I

  rw [e]
  by_cases ha' : (a : ℕ) < p <;> by_cases hb' : (b : ℕ) < p
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]
  · rw [if_neg (by omega), if_pos (by omega), zero_add]
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]

theorem gen_kill_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}
    (hX : IsGen ψ om θ τ X GX) (hY : IsGen ψ om θ τ (Complex.I • (cart M τ * X)) GY)
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f)
    (h0 : (GX + Complex.I • GY) f = 0) {P : MvPolynomial (FVar D T.rank S.rank) ℂ}
    (hP : ∀ a b : Fin T.rank, p ≤ (a : ℕ) → (b : ℕ) < p →
      ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) :
    (GX + Complex.I • GY) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (BT) f P) = 0 := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨ν, n0, hν⟩ := exists_coef_any hB hBT lX lY ha
  unfold pureTensorO aPlusAll
  refine (quad_pure (P := IsThetaFunO ψ S T) (G := GX + Complex.I • GY)
    (B := fun k g => ((fockScale D k.1 : ℂ)⁻¹ * (if k.1 = τ then (1 : ℂ) else 0)) •
      (annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) (X * unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g +
        (-Complex.I) • annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ))
          (X * cplxO 1 (cart M k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) g))
    (μ := fun i j => if i.1 = τ then if j.1 = τ then if i.2.2 = j.2.2 then
      ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * ν i.2.1 j.2.1 else 0 else 0 else 0)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf ?_ h0 P).trans ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · intro i g g' hg hg'
    rw [annih_add hψ hθ _ _ _ hg hg', annih_add hψ hθ _ _ _ hg hg']
    simp only [smul_add]
    abel
  · intro i a g hg
    rw [annih_smul hψ hθ _ _ _ _ hg, annih_smul hψ hθ _ _ _ _ hg, smul_comm _ a, ← smul_add, smul_comm _ a]
  · rintro ⟨τ₁, a, c⟩ ⟨τ₂, b, d⟩ g hg
    have ta := fun z => annih_theta hψ hθ τ (cplxO 1 (cart M τ)) z hg
    have aa := fun z => annih_aPlus (sS := fun _ => 1) hψ hθ τ z hS hT τ₂ (unitMap (BS τ₂) (BT τ₂) b d) hg
    dsimp only at aa ⊢
    rw [aa, aa, aPlus_smul hψ hθ _ _ _ _ (theta_add (ta _) (theta_smul _ (ta _))),
      aPlus_add hψ hθ _ _ _ (ta _) (theta_smul _ (ta _)), aPlus_smul hψ hθ _ _ _ _ (ta _), smul_add (-Complex.I),
      add_add_add_comm, smul_add, smul_smul, ← add_smul, smul_smul]
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    by_cases e1 : τ₁ = τ
    swap
    · simp only [if_neg e1, ite_self, mul_zero, zero_mul, add_zero]
    by_cases e2 : τ₂ = τ
    swap
    · simp [e2, omDir, Ne.symm e2]
    subst e1
    subst e2
    have := hν a c b d _ rfl _ rfl
    simp only [if_true]
    by_cases e3 : c = d
    · simp only [if_pos e3, if_pos e3.symm] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
    · simp only [if_neg e3, if_neg (Ne.symm e3)] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
  · exact fun i _ h => gen_aPlus hψ hθ hX hY _ _ _ h
  · intro i
    rw [hv, hv, smul_zero, add_zero, smul_zero]
  · refine (congrArg _ ?_).trans (map_zero _)
    simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.smul_sum]
    by_cases hab : p ≤ (a : ℕ) ∧ (b : ℕ) < p
    · rw [hP a b hab.1 hab.2, smul_zero]
    · rw [n0 a b hab, mul_zero, zero_smul]

end Model

theorem rderC_theta_eq_zero_any : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → S.SigOK → T.SigOK → ∀ (BS : D.what₂.Tau → Mt S.rank), (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (p : D.what₂.Tau → ℕ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsONBasis (gramAt D T τ) (cart M τ) (BT τ) (p τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ (P : PolF D T.rank S.rank) τ, (∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) → ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P)) = 0 := by
  intro D ψ S T χS χT om hom θ hθ kS kT BS hBS Sp M p BT hBT f hf hv P τ hP Z hZ h
  have hψ := hom.std
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨h1, h2⟩ := pMinus_laws hZ
  obtain ⟨ha, eY⟩ := parts (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) (hT τ) h1 h2
  obtain ⟨lX, lY⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  unfold RderC
  unfold conjAt at lX lY ⊢
  rw [eY] at lY ⊢
  generalize (1 / 2 : ℂ) • (Z + -((gramAt D T τ)⁻¹ * Zᴴ * gramAt D T τ)) = X at ha lX lY
  obtain ⟨GX, hX⟩ : ∃ G, IsGen ψ om θ τ X G := _root_.GlobalTheory.DefLift.Gen.exists_generator D ψ S T χS χT om hom θ hθ τ _ lX
  obtain ⟨GY, hY⟩ : ∃ G, IsGen ψ om θ τ (Complex.I • (cart M τ * X)) G :=
    _root_.GlobalTheory.DefLift.Gen.exists_generator D ψ S T χS χT om hom θ hθ τ _ lY
  have hφ : IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) :=
    pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
      (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
  have key := gen_kill_any hψ hθ hB (hBT τ) hX hY lX lY ha hf (hv τ)
    (gen_kill_vac hom hθ kS kT hS hT hX hY lX lY ha hf hv) hP
  generalize pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P = φ at key hφ
  funext g
  have a1 := ((hX φ hφ).2.2.2 (h, g) 0).deriv
  have a2 := ((hY φ hφ).2.2.2 (h, g) 0).deriv
  simp only [Prod.mk_mul_mk, mul_one] at a1 a2
  have a3 := congrFun (congrArg (om (h, g)) key) 0
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul, map_zero] at a3
  simp only [Pi.add_apply, Pi.smul_apply, Rder, thetaKO]
  rw [a1, a2]
  exact a3

theorem rderC_ptAt_delta_eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus (R.MW i σ) τ, ∀ h, RderC R.θ (Wc D i) τ Z (fun g => thetaKO om h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f (deltaAtEmb D i σ))) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m om BW f₀ f c io hL τ Z hZ h
  obtain ⟨hCore, -, -, -, -, hW, hBW, hLV, -⟩ := id hL
  have hf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m om BW f₀ f c io hL).1
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hLV
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq hth hv.theta hf (hv.fock τ)
  have hpq : ∀ ρ, pW D i ρ + qW D i ρ ≤ (Vc D i).rank := fun ρ =>
    (sig_sum _ (D.sp.W_sig _) (tauE D ρ)).trans_le ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i))
  have hP := GlobalTheory.MinorHarmonic.laplacian_delta D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ) hpq τ
  exact rderC_theta_eq_zero_any D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) om hW R.θ hv.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hCore.models.BV i) _ (R.MW i σ) (pW D i) BW hBW f hf hvac (deltaAtEmb D i σ) τ hP Z hZ h

end GlobalTheory.LowKillDelta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegral
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertKatFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latAt_entry_at {n : ℕ} (X : Spc F E n) (v : Pl (F := F)) {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt X v) (i : Fin n) : At (evFin F v) (z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hx
    intro u hu
    have h0 := ha u hu
    rw [smul_eq_mul] at h0
    simp only [Pi.smul_apply]
    rw [smul_smul, h0, zero_smul]
  | zero => intro u _; simp
  | add x y _ _ hx hy => intro u hu; simp [smul_add, hx u hu, hy u hu]
  | neg x _ hx => intro u hu; simp [smul_neg, hx u hu]

theorem mulVec_mem_latAt {n : ℕ} (X : Spc F E n) (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (hsurj : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (P : GL (Fin n) L) (hP : ∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v)
    (K : Matrix (Fin n) (Fin n) L) (hK : ∀ i j, K i j ∈ Formalism.UG.intL L)
    (A : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hA : A = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι)
    (z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hz : z ∈ GlobalTheory.InertSph.latAt X v) : A *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
  obtain ⟨y, rfl⟩ : ∃ y : Fin n → L, z = fun i => ι (y i) :=
    ⟨fun i => GlobalTheory.InertLocFrame.pre ι (z i), funext fun i =>
      (GlobalTheory.InertLocFrame.pre_spec ι ((hsurj _).1 (latAt_entry_at X v hz i))).symm⟩
  obtain ⟨x, rfl⟩ : ∃ x : Fin n → L, y = (P : Matrix (Fin n) (Fin n) L) *ᵥ x := by
    refine ⟨((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hx := (hP x).2 hz
  have hKx : ∀ i, (K *ᵥ x) i ∈ Formalism.UG.intL L := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hK i j) (hx j)
  have key : A *ᵥ (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) =
      fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ (K *ᵥ x)) i) := by
    set N := (P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hN
    set Y := (P : Matrix (Fin n) (Fin n) L) *ᵥ x with hY
    have h1 : (1 - ι 1) • (fun i => ι (Y i)) = 0 := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [sub_mul, one_mul, ← hmul, one_mul, sub_self]
    have h2 : N.map ι *ᵥ (fun i => ι (Y i)) = fun i => ι ((N *ᵥ Y) i) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [hmul]
    have h3 : N *ᵥ Y = (P : Matrix (Fin n) (Fin n) L) *ᵥ (K *ᵥ x) := by
      rw [hY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hA, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add, h2, h3]
  rw [key]
  exact (hP _).1 hKx

theorem mem_KAt_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∀ (g : UA σ X.J) (K K' : Matrix (Fin n) (Fin n) L), (∀ i j, K i j ∈ Formalism.UG.intL L) →
        (∀ i j, K' i j ∈ Formalism.UG.intL L) →
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        mat g⁻¹ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K' * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        g ∈ GlobalTheory.InertSph.KAt σ X v := by
  intro F E _ _ _ _ _ σ v n X L _ _ ι _hinj hsurj hmul _hint P hP g K K' hK hK' hg hg'
  refine ⟨?_, fun z hz => ⟨mulVec_mem_latAt X v ι hsurj hmul P hP K hK _ hg z hz,
    mulVec_mem_latAt X v ι hsurj hmul P hP K' hK' _ hg' z hz⟩⟩
  have hsup : ∀ w u, evFin F v u = 0 → u • ι w = 0 := fun w => (hsurj (ι w)).2 ⟨w, rfl⟩
  intro u hu
  set N := (P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have hm : mat g - 1 = (N - 1).map ι := by
    rw [hg]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply, map_sub]
      ring
    · simp [Matrix.one_apply, hij]
  rw [hm]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  exact hsup _ u hu

end GlobalTheory.InertKatFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSum
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem nat_card_monoDeg_fin (D a : ℕ) (hD : 1 ≤ D) :
    Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  classical
  rw [Nat.card_eq_fintype_card, MonoDeg.card_eq_card_finsuppAntidiag,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show a + (d + 1) - 1 = a + d by omega, show d + 1 + a - 1 = a + d by omega,
    show d + 1 - 1 = d by omega]
  exact Nat.choose_symm_add

theorem sum_range_choose_mul_sub (d n : ℕ) :
    ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) = (n + d + 1).choose (d + 2) := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    have h1 : ∑ a ∈ Finset.range n, (a + d).choose d * (n + 1 - a) =
        ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) +
          ∑ a ∈ Finset.range n, (a + d).choose d := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < n := Finset.mem_range.mp ha
      rw [show n + 1 - a = (n - a) + 1 by omega, Nat.mul_succ]
    rw [Finset.sum_range_succ, h1, ih, show n + 1 - n = 1 by omega, mul_one, add_assoc,
      ← Finset.sum_range_succ, Nat.sum_range_add_choose,
      show n + 1 + d + 1 = (n + d + 1) + 1 by omega, Nat.choose_succ_succ' (n + d + 1) (d + 1)]
    ring_nf

theorem monomial_counts : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T →
    (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧
    Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧
    (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) =
      (T - 1).choose D * (T + D * (D + 1)) := by
  intro D T hD hT
  have h1 := fun a => nat_card_monoDeg_fin D a hD
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, T = d + 2 + m := ⟨T - (d + 2), by omega⟩
  have hTD : d + 2 + m - (d + 1) = m + 1 := by omega
  have hT1 : d + 2 + m - 1 = m + d + 1 := by omega
  have hsub : ∀ a, a + (d + 1) - 1 = a + d := fun a => by omega
  simp only [hsub, show d + 1 - 1 = d by omega] at h1 ⊢
  have hsum : ∑ a ∈ Finset.range (m + 1), (a + d).choose d = (m + d + 1).choose (d + 1) :=
    Nat.sum_range_add_choose m d
  refine ⟨h1, ?_, ?_⟩
  · rw [Nat.card_sigma, hT1]
    simp only [h1]
    rw [← hsum, hTD, Finset.sum_range (fun a => (a + d).choose d)]
  · rw [hTD, hT1]
    have hw : ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (d + 2 + m - a) =
        ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (m + 1 - a) +
          (d + 1) * ∑ a ∈ Finset.range (m + 1), (a + d).choose d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < m + 1 := Finset.mem_range.mp ha
      rw [show d + 2 + m - a = (m + 1 - a) + (d + 1) by omega]
      ring
    rw [hw, sum_range_choose_mul_sub, hsum]
    have key := Nat.add_one_mul_choose_eq (m + d + 1) (d + 1)
    rw [show m + 1 + d + 1 = m + d + 1 + 1 by omega]
    nlinarith [key]

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefBigSecondBaseChange
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem nef_big_second_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.L₂ → IsBig F X.L₂ → IsNef E (X.baseChange E).L₂ ∧ IsBig E (X.baseChange E).L₂ := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨PosBaseChange.isNef_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hn,
    PosBaseChange.isBig_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hb⟩

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegmentStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ), n * n = 0 → (∀ τ : ℝ, (u τ).val = 1 + τ • n) → (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) → ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  first | exact @GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | exact GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | (intros; apply GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompAlt
section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp (D.OEp p)} {s₂ : S₂ ⟶ Sp (D.OEp p)} {s₃ : S₃ ⟶ Sp (D.OEp p)}
  {o₁ : Obj D p N s₁} {o₂ : Obj D p N s₂} {o₃ : Obj D p N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

def ObjMap.comp (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  act a := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.PP.isLB (pull_isLB o₂.PP.isLB m₁.φ) (pull_isLB o₃.PP.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.PP.L m₁.φ)
      (chartPullSame o₃.PP.L (fun _ : PUnit => m₁.φ ≫ m₂.φ) (fun _ => m₂.φ) (fun _ => 1) m₁.φ (fun _ => rfl))
      m₂.pol)
  eta a := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem objMap_comp : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp (D.OEp p)) (s₂ : S₂ ⟶ Sp (D.OEp p)) (s₃ : S₃ ⟶ Sp (D.OEp p))
    (o₁ : GlobalTheory.UPel.Obj D p N s₁) (o₂ : GlobalTheory.UPel.Obj D p N s₂) (o₃ : GlobalTheory.UPel.Obj D p N s₃) (f : S₁ ⟶ S₂)
    (g : S₂ ⟶ S₃), GlobalTheory.UPel.ObjMap o₁ o₂ f → GlobalTheory.UPel.ObjMap o₂ o₃ g → Nonempty (GlobalTheory.UPel.ObjMap o₁ o₃ (f ≫ g)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m₁ m₂ => ⟨m₁.comp m₂⟩

end GlobalTheory.UPel
end
end

