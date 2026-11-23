module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.TypeRec.Model

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG

section Compl
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [hp : Fact p.Prime]

theorem emb_surjective (hw : (p : 𝓞 F) ∈ w.asIdeal) (h2 : (p : 𝓞 F) ∉ w.asIdeal ^ 2)
    (hN : Ideal.absNorm w.asIdeal = p) : Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb w p hw) := by
  let K := w.adicCompletion F
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hres : ∀ a : 𝓞 F, ∃ m : ℤ, a - m ∈ w.asIdeal := by
    intro a
    haveI := Formalism.BasicNotions.Examples₂.LocF.finite_quot w
    letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
    have hc : Fintype.card (𝓞 F ⧸ w.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    obtain ⟨z, hz⟩ := (ZMod.ringEquivOfPrime (𝓞 F ⧸ w.asIdeal) hp.out hc).surjective (Ideal.Quotient.mk _ a)
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
    rw [map_intCast] at hz
    exact ⟨m, Ideal.Quotient.eq.1 (by rw [map_intCast, hz])⟩
  have hvp : WithZero.exp (-1 : ℤ) ≤ Valued.v (p : K) := by
    have e : (p : K) = algebraMap F K (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [e, adic_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have h3 : ¬ w.intValuation (p : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
      h2 ((w.intValuation_le_pow_iff_mem _ 2).1 h)
    have h0 : w.intValuation (p : 𝓞 F) ≠ 0 := w.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h3 ⊢
    omega
  have step : ∀ y : K, Valued.v y ≤ 1 → ∃ (m : ℤ) (z : K), Valued.v z ≤ 1 ∧ y = m + p * z := by
    intro y hy
    obtain ⟨a, ha⟩ := adic_exists_approx w y hy
    obtain ⟨m, hm⟩ := hres a
    rw [adic_algebraMap_R] at ha
    have h1 : Valued.v (algebraMap F K (algebraMap (𝓞 F) F (a - m))) < 1 := by
      rw [adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem _).2 hm
    have h4 : Valued.v (y - m) < 1 := by
      have := Valuation.map_add_lt _ ha h1
      rwa [map_sub, map_sub, map_intCast, map_intCast, sub_add_sub_cancel] at this
    refine ⟨m, (y - m) / p, ?_, by rw [mul_div_cancel₀ _ hp0, add_sub_cancel]⟩
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0))]
    refine le_trans ?_ hvp
    by_cases h0 : Valued.v (y - m) = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  have iter : ∀ (n : ℕ) (y : K), Valued.v y ≤ 1 → ∃ (m : ℤ) (z : K), Valued.v z ≤ 1 ∧ y = m + (p : K) ^ n * z := by
    intro n y hy
    induction n with
    | zero => exact ⟨0, y, hy, by simp⟩
    | succ n ih =>
      obtain ⟨m, z, hz, e⟩ := ih
      obtain ⟨m', z', hz', e'⟩ := step z hz
      exact ⟨m + p ^ n * m', z', hz', by rw [e, e', Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]; ring⟩
  letI := (Formalism.BasicNotions.Examples₂.LocF.emb w p hw).toAlgebra
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ (Formalism.BasicNotions.Examples₂.LocF.emb_cont w p hw)
  have hcl : IsClosed (Set.range (Formalism.BasicNotions.Examples₂.LocF.emb w p hw)) :=
    (LinearMap.range (Algebra.linearMap ℚ_[p] K)).closed_of_finiteDimensional
  have hlt := Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w p hw
  have hint : ∀ y : K, ‖y‖ ≤ 1 → y ∈ Set.range (Formalism.BasicNotions.Examples₂.LocF.emb w p hw) := by
    intro y hy
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    obtain ⟨m, z, hz, e⟩ := iter n y (Valued.toNormedField.norm_le_one_iff.1 hy)
    refine ⟨m, ⟨m, map_intCast _ _⟩, ?_⟩
    rw [dist_eq_norm, e, add_sub_cancel_left, norm_mul, norm_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (Valued.toNormedField.norm_le_one_iff.2 hz)) hn
  intro y
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (‖y‖ + 1)⁻¹ by positivity) hlt
  obtain ⟨x, hx⟩ := hint ((p : K) ^ n * y) (by
    rw [norm_mul, norm_pow]
    have h1 : ‖(p : K)‖ ^ n * (‖y‖ + 1) ≤ 1 := by
      rw [← le_div_iff₀ (by positivity), one_div]; exact hn.le
    nlinarith [pow_nonneg (norm_nonneg (p : K)) n])
  refine ⟨x / (p : ℚ_[p]) ^ n, ?_⟩
  rw [map_div₀, hx, map_pow, map_natCast]
  field_simp

end Compl

theorem nonempty_ident (D : D7) : Nonempty (Ident D) := by
  have key : ∀ k v, Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb (D.naut.plGw k v) (D.host.g k) (D.naut.plGw_over k v)) := by
    intro k v
    refine emb_surjective _ _ _ (fun h => ?_)
      (by
        simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
          (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)))
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime k).ne_zero
    have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
    have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h)
    exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
  exact ⟨⟨fun k v => RingEquiv.ofBijective _ ⟨RingHom.injective _, key k v⟩,
    fun k v => Formalism.BasicNotions.Examples₂.LocF.emb_cont _ _ (D.naut.plGw_over k v)⟩⟩

theorem cls_eq_of_iso {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : Nonempty (pull I k v σ ≅ pull I k v τ)) : GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls τ := by
  obtain ⟨e⟩ := h
  have e' := Representation.equivOfIso e
  refine congrArg (Sigma.mk n) (GlobalTheory.SmGL.IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk e'.toLinearEquiv fun g => ?_⟩)
  have hg : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom g) = g :=
    Units.ext (Matrix.ext fun a b => (I.i k v).apply_symm_apply _)
  rw [← hg]
  exact e'.toIntertwiningMap.isIntertwining' _


theorem map_surj {D : D7} (I : Ident D) (k v) (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).toRingHom) := fun g =>
  ⟨Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom g,
    Units.ext (Matrix.ext fun _ _ => (I.i k v).apply_symm_apply _)⟩

theorem irrSm_pull {D : D7} (I : Ident D) (k v) {n : ℕ} (σ) : GlobalTheory.SerSys.IrrSm (pull I k v (n := n) σ) := by
  refine ⟨(GlobalTheory.GLp.Model.isIrrRep_iff _).2 (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp σ.irr _ (map_surj I k v n)), fun x => ?_⟩
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => (I.cont k v).comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => (I.cont k v).comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  exact (σ.smooth x).preimage hc

theorem emb_le {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
    (f : ℚ_[p] →+* w.adicCompletion F) (hf : Continuous f) (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : ‖f t‖ ≤ 1 := by
  have hd : DenseRange (Int.cast : ℤ → ℤ_[p]) := PadicInt.denseRange_intCast
  refine hd.induction_on (p := fun z : ℤ_[p] => ‖f z‖ ≤ 1) ⟨t, ht⟩
    (isClosed_le (hf.comp continuous_subtype_val).norm continuous_const) fun m => ?_
  simpa using Formalism.BasicNotions.Examples₂.LocF.norm_int_le w m

theorem exists_pull {D : D7} (I : Ident D) (k v) {n : ℕ} (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (h : GlobalTheory.SerSys.IrrSm π) : ∃ σ, Nonempty (π ≅ pull I k v σ) := by
  letI := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  have hi : Continuous (I.i k v).symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).symm.toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨⟨π, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom), fun x => (h.2 x).preimage hc,
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp ((GlobalTheory.GLp.Model.isIrrRep_iff _).1 h.1) _ fun g => ⟨_, hg g⟩⟩,
    ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ π) fun g => LinearMap.ext fun x => ?_)⟩⟩
  change π.ρ g x = π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
  rw [hg]

end GlobalTheory.TypeRec.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
section
noncomputable section

namespace GlobalTheory.PendOf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.NPin ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def IsConjGen (D : D7) (w w' : PlE D.host) (γ γ' : GE D.nd) : Prop :=
  ∃ c : D.nd.Om ≃+* D.nd.Om,
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') ∧ ∀ y, γ' (c y) = c (γ y)

def LabAll (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Prop :=
  ∃ γ : Fin 2 → PlE D.host → GE D.nd, (∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    (∀ k v w', IsConjPl D.host (D.naut.plGw k v) w' →
      IsConjGen D (D.naut.plGw k v) w' (D.ntypes.tg k v) (γ k w')) ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ a : D.naut.LP w,
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (γ k w) (T.e w a)

def gPl (D : D7) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ kv : (Σ k : Fin 2, D.nd.PlG k), NG.OverPl (D.naut.plGw kv.1 kv.2) v}

def IsLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (r p : ℕ)
    (g : GL (Fin r) (ZMod p)) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Prop :=
  ∀ a b : Fin n,
    if hab : a.val < r ∧ b.val < r then
      Valued.v (h.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val :
        s.v.adicCompletion (maximalRealSubfield L))) < 1
    else h.val a b = if a = b then 1 else 0

def IsTypeGroupBlockLift (D : D7) (n : ℕ) (L : G0g D.nd → GAf D.host.E n) : Prop :=
  ∀ g : G0g D.nd, TrivOutside (gPl D) (L g) ∧
    ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
      IsLiftAt s D.R.r (D.host.g kv.1) (g kv) (s.loc n (L g))

def actSum (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (L : G0g D.nd → GAf D.host.E n)
    (z : MonoidAlgebra ℂ (G0g D.nd)) (f : GAf D.host.E n → W) : GAf D.host.E n → W :=
  z.coeff.sum fun g c => c • NG.rt D.host.E n (L g) f

def GreenLab {D : D7} (Γ : GrpSide D) : Prop :=
  ∀ (k : Fin 2) (d : ℕ), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ τ : FDRep ℂ (GL (Fin d) (ZMod (D.host.g k))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod (D.host.g k)) τ →
      Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)) τ
        ((Γ.O k).lab d τ)

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def IsLiftN {n r p : ℕ} (g : GL (Fin r) (ZMod p)) (h : GL (Fin n) F) : Prop :=
  ∀ a b : Fin n,
    if hab : a.val < r ∧ b.val < r then
      valuation F (h.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : F)) < 1
    else h.val a b = if a = b then 1 else 0

def NotKilled {n r p : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) F) W)
    (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (v : W) : Prop :=
  ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin n) F, (∀ g, IsLiftN g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (ℓ g) v) ≠ 0

def IsLevelOne {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) F) W) (v : W) : Prop :=
  ∀ h : GL (Fin n) F, (∀ a b, valuation F (h.val a b - if a = b then 1 else 0) < 1) → π h v = v

end Local

def labAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) n) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) n π)

def InSeries (D : D7) (k : Fin 2) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  CategoryTheory.Simple ρ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ

def idemOf (D : D7) (k : Fin 2) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ

def RegLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r) ρ f, InSeries D k ρ f →
    Squarefree f → (∃ x, IsLevelOne π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (rcAt hL D (D.naut.plGw k v) D.R.r π).mono0 ∧ labAt hL D k v π = f

def SplitLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    ∃ (π₁ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r)
      (π₂ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin D.R.t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (idemOf D k ρ) y

def LocDZ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → Squarefree f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (rcAt hL D (D.naut.plGw k v) _ π).mono0 ∧ labAt hL D k v π = f * (X - C u) ^ D.R.t

def ConjDual (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (w' : PlE D.host),
    IsConjPl D.host (D.naut.plGw k v) w' → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) → D.naut.mono0 (D.naut.locV i PI w')) ∧
    (TameLP D (D.naut.locV i PI (D.naut.plGw k v)) → TameLP D (D.naut.locV i PI w')) ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)))).map (·⁻¹)

end GlobalTheory.PendOf

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MeetsReferenceOfMeetsAll
section
noncomputable section

namespace GlobalTheory.TwInputs.EigModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.Triple (heckeVal satake muBase)

variable {D : D7}

variable {cf : CharFrame D} {Rw : RowSide D} {Sb : Finset (PlE D.host)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}

theorem sig_all_of (hN : NoFormsOff D) (hM : MeetsAll D) (hC : CommAll D)
    (hall : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, GlobalTheory.EigTie.IsEigSys D.nexp i j b ev →
      ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, HkIdx i k P → GlobalTheory.EigTie.sigEv s k P = ev k P) :
    D.nexp.sig_all := by
  intro i j b x ev hx he hk
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · let W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
      Eigsp D.nexp i j b ev ⊓ LinearMap.ker (eG D.nexp i j b - LinearMap.id)
    have mW : ∀ y, y ∈ W ↔ (∀ k P, HkIdx i k P → D.nexp.hkF i j b k P y = ev k P • y) ∧ eG D.nexp i j b y = y := by
      intro y
      simp only [W, Eigsp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hxW : x ∈ W := (mW x).2 ⟨fun k P h => hk k P h.1 h.2.1 h.2.2.1 h.2.2.2, he⟩
    have hst : GStable D.nexp i j b W := by
      intro g y hy
      obtain ⟨a, c⟩ := (mW y).1 hy
      refine (mW _).2 ⟨fun k P h => by rw [hC i j hj b k P h, a k P h, map_smul], ?_⟩
      have e := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
        (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
        (D.nexp.eAlg_central i b (MonoidAlgebra.of _ _ g))
      rw [map_mul, map_mul, MonoidAlgebra.lift_of] at e
      have e2 := LinearMap.congr_fun e y
      change eG D.nexp i j b (D.nexp.actG i j b g y) = D.nexp.actG i j b g (eG D.nexp i j b y) at e2
      rw [e2, c]
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1
      (hM i j b W ((Submodule.ne_bot_iff _).2 ⟨x, hxW, hx⟩) hst fun y hy => ((mW y).1 hy).2)
    obtain ⟨a, c⟩ := (mW y).1 hy1
    obtain ⟨s, e1, e2, e3⟩ := hall i j hj b ev ⟨y, ⟨y, hy2, c⟩, hy0, a⟩
    exact ⟨s, e1, e2, fun k P p q r t => e3 k P ⟨p, q, r, t⟩⟩
  · exact absurd ((hN i j hj b).elim x 0) hx

section Laws

open GlobalTheory.SupLaw.Model

variable (D) (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

end Laws

end GlobalTheory.TwInputs.EigModel

end
end

