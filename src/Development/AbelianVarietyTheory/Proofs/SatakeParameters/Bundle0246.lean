module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.KernelLattices.TopPin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverP
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (ha : a ∈ v.adicCompletionIntegers F) (c : v.adicCompletion F) (hc0 : c ≠ 0) (hc : Valued.v c ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) ≤ Valued.v c := by
  have hopen : IsOpen {x : v.adicCompletion F |
      (x - a) * c⁻¹ ∈ (Valued.v.valuationSubring : ValuationSubring (v.adicCompletion F))} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      ((continuous_sub_right _).mul continuous_const)
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := F)).exists_mem_open hopen ⟨a, by simp⟩
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  have hy' : Valued.v (algebraMap F (v.adicCompletion F) y - a) ≤ Valued.v c := by
    have h1 : Valued.v ((algebraMap F (v.adicCompletion F) y - a) * c⁻¹) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff _ _).1 hy
    rw [map_mul, map_inv₀] at h1
    have h2 := mul_le_mul' h1 (le_refl (Valued.v c))
    rwa [mul_assoc, inv_mul_cancel₀ hvc, mul_one, one_mul] at h2
  have ha1 : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha
  have e2 : ∀ z : F, Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z := fun z =>
    v.valuedAdicCompletion_eq_valuation' z
  have hy1 : v.valuation F y ≤ 1 := by
    rw [← e2]
    have e : algebraMap F (v.adicCompletion F) y = (algebraMap F (v.adicCompletion F) y - a) + a := by ring
    rw [e]
    exact Valuation.map_add_le _ (hy'.trans hc) ha1
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hy1 (Units.mk0 (Valued.v c) hvc)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) ≤ Valued.v c := by
    rw [← map_sub, e2]
    exact hr.le
  have e : a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) =
      -(algebraMap F (v.adicCompletion F) y - a) - (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hr')
  rw [Valuation.map_neg]; exact hy'

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem iw_algebraMap (A : LocAt F E n G) (hA : SplAlg A) (v : Fin G.P.nV) (f : F) :
    A.iw v (algebraMap F E f) = (A.eQ v).symm (algebraMap F ((A.pl v).1.adicCompletion F) f) := by
  have h1 : inclE (F := F) ((A.pl v).1.adicCompletion F) (algebraMap F E f) =
      (1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f := by
    change algebraMap F E f ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  simp only [LocAt.iw, LocAt.phE, LocAt.ph, RingHom.comp_apply, h1]
  rw [show (A.spl v).toRingHom ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) =
    A.spl v ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) from rfl, hA v]
  rfl

theorem iw_int (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    A.iw v (x : E) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  haveI := (G.P.setting v).frac_alt
  have h1 : IsIntegral ℤ (A.iw v (x : E)) := x.2.map (A.iw v).toIntAlgHom
  have h2 : IsIntegral (G.P.W v) (A.iw v (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def toW (A : LocAt F E n G) (v : Fin G.P.nV) : 𝓞 E →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  (RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h),
        (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩).symm.toRingHom.comp
    (((A.iw v).comp (algebraMap (𝓞 E) E)).codRestrict _ (fun x => iw_int A v x))

theorem toW_spec (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    algebraMap (G.P.W v) (G.P.Qq v) (toW A v x) = A.iw v (x : E) := by
  haveI := (G.P.setting v).frac_alt
  set e := RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h),
        (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩ with he
  have h : (e (toW A v x) : G.P.Qq v) = A.iw v (x : E) := by
    simp only [toW, he, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, RingHom.codRestrict_apply]
  rw [← h]
  rfl

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem p_irr (v : Fin G.P.nV) : Irreducible ((p : ℕ) : G.P.W v) := (G.P.setting v).p_unif

def primeAt (A : LocAt F E n G) (v : Fin G.P.nV) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (toW A v) (Ideal.span {((p : ℕ) : G.P.W v)})
  isPrime := by
    haveI : (Ideal.span {((p : ℕ) : G.P.W v)}).IsPrime :=
      (Ideal.span_singleton_prime (p_irr (G := G) v).ne_zero).2 (p_irr (G := G) v).prime
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hm : ((p : ℕ) : 𝓞 E) ∈ Ideal.comap (toW A v) (Ideal.span {((p : ℕ) : G.P.W v)}) := by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _
    rw [h, Ideal.mem_bot] at hm
    have hp0 : ((p : ℕ) : G.P.W v) = 0 := by
      have := congrArg (toW A v) hm; rwa [map_natCast, map_zero] at this
    exact (p_irr (G := G) v).ne_zero hp0

theorem mem_primeAt (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    x ∈ (primeAt A v).asIdeal ↔ ((p : ℕ) : G.P.W v) ∣ toW A v x := by
  change x ∈ Ideal.comap (toW A v) _ ↔ _
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]

theorem exists_primeOf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ)
    [Fact p.Prime] (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, ∃ P : HeightOneSpectrum (𝓞 E),
    PrimeOf p (G.P.W v) (A.iw v) P ∧
    (∀ (y : G.P.W v) (k : ℕ), ∃ (x : 𝓞 E) (z : G.P.W v), A.iw v x = algebraMap _ _ (y + (p : G.P.W v) ^ k * z)) ∧
    ((p : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro F E _ _ _ _ _ n p _ G A hW hA v
  refine ⟨primeAt A v, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨toW A v x, (toW_spec A v x).symm, mem_primeAt A v x⟩
  · intro y k
    set K := (A.pl v).1.adicCompletion F
    have ha : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y) ∈ (A.pl v).1.adicCompletionIntegers F :=
      (hW v _).1 ⟨y, rfl⟩
    have hpK : ((p : ℕ) : K) ≠ 0 := by
      rw [← map_natCast (algebraMap F K)]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have hc0 : ((p : ℕ) : K) ^ k ≠ 0 := pow_ne_zero _ hpK
    have hp1 : Valued.v ((p : ℕ) : K) ≤ 1 := by
      have e2 : Valued.v (algebraMap F K ((p : ℕ) : F)) = (A.pl v).1.valuation F ((p : ℕ) : F) :=
        (A.pl v).1.valuedAdicCompletion_eq_valuation' _
      rw [← map_natCast (algebraMap F K), e2, ← map_natCast (algebraMap (𝓞 F) F)]
      exact (A.pl v).1.valuation_le_one _
    have hc : Valued.v (((p : ℕ) : K) ^ k) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le' hp1
    obtain ⟨r, hr⟩ := exists_int_near (A.pl v).1 _ ha _ hc0 hc
    set a := A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y)
    set d := a - algebraMap F K (algebraMap (𝓞 F) F r)
    have hdq : d * (((p : ℕ) : K) ^ k)⁻¹ ∈ (A.pl v).1.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      have hv0 : Valued.v (((p : ℕ) : K) ^ k) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
      calc Valued.v d * (Valued.v (((p : ℕ) : K) ^ k))⁻¹ ≤ Valued.v (((p : ℕ) : K) ^ k) * (Valued.v (((p : ℕ) : K) ^ k))⁻¹ :=
            mul_le_mul' hr le_rfl
        _ = 1 := mul_inv_cancel₀ hv0
    obtain ⟨z', hz'⟩ := (hW v ((A.eQ v).symm (d * (((p : ℕ) : K) ^ k)⁻¹))).2 (by rwa [RingEquiv.apply_symm_apply])
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, -z', ?_⟩
    have hx : ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F r) := by
      change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [hx, iw_algebraMap A hA v]
    have e1 : algebraMap F K (algebraMap (𝓞 F) F r) = a - (((p : ℕ) : K) ^ k) * (d * (((p : ℕ) : K) ^ k)⁻¹) := by
      rw [mul_comm d, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; simp [d]
    rw [e1, map_sub, map_mul, map_pow, map_natCast, ← hz', RingEquiv.symm_apply_apply]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_neg]
    ring
  · rw [mem_primeAt, map_natCast]
  · intro h
    have h1 : toW A v ((p : ℕ) : 𝓞 E) ∈ Ideal.map (toW A v) ((primeAt A v).asIdeal ^ 2) := Ideal.mem_map_of_mem _ h
    rw [Ideal.map_pow, map_natCast] at h1
    have h2 : Ideal.map (toW A v) (primeAt A v).asIdeal ^ 2 ≤ (Ideal.span {((p : ℕ) : G.P.W v)}) ^ 2 :=
      Ideal.pow_right_mono (Ideal.map_comap_le) 2
    have h3 := h2 h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
    have hi := p_irr (G := G) v
    obtain ⟨c, hc⟩ := h3
    have : ((p : ℕ) : G.P.W v) * (((p : ℕ) : G.P.W v) * c) = ((p : ℕ) : G.P.W v) * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
    have hu := mul_left_cancel₀ hi.ne_zero this
    exact hi.not_isUnit ⟨⟨_, c, hu, by rw [mul_comm]; exact hu⟩, rfl⟩

end GlobalTheory.TwV.Xc.PrimeAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open scoped Pointwise

namespace GlobalTheory.AboveL

theorem mem_dec_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) :
    g ∈ Dec (F := K) A ↔ g' ∈ Dec (F := K') A := by
  have key : ((g • A : ValuationSubring Ω) : Set Ω) = ((g' • A : ValuationSubring Ω) : Set Ω) := by
    rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
    ext x
    simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]
  unfold Dec
  rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h; apply SetLike.coe_injective; rw [← key]; exact congrArg _ h
  · intro h; apply SetLike.coe_injective; rw [key]; exact congrArg _ h

theorem exists_cm_solvable_split : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  intro Ω _ E _ _ _ _ _ A w h N hN
  let F := maximalRealSubfield E
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := Ideal.comap_ne_bot_of_integral_mem hx₀0 hx₀ (Algebra.IsIntegral.isIntegral x₀) }
  have hv : IsPlaceOver A v := by
    intro x
    show _ ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal
    rw [← h]
    rfl
  obtain ⟨T, hvT, hlift⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hN

  let φ := IsScalarTower.toAlgHom F E Ω
  let K : IntermediateField F Ω := φ.fieldRange
  haveI : FiniteDimensional F K := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  have hK : ∀ g : G F Ω, g ∈ K.fixingSubgroup ↔ ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x; exact hg _ ⟨x, rfl⟩
    · rintro hg _ ⟨x, rfl⟩; exact hg x
  let V : Subgroup (Dec (F := F) A) := K.fixingSubgroup.subgroupOf (Dec (F := F) A)
  have hVo : IsOpen (V : Set (Dec (F := F) A)) := by
    rw [Subgroup.coe_subgroupOf]
    exact K.fixingSubgroup_isOpen.preimage continuous_subtype_val
  haveI : Fact (Nat.card (E ≃ₐ[F] E)).Prime :=
    ⟨by rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F E]; exact Nat.prime_two⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card rfl
  have habel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ := fun σ τ => (IsCyclic.commGroup).mul_comm σ τ
  have hcomm : commutator (Dec (F := F) A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mem_subgroupOf, hK]
    intro x
    have h1 : AlgEquiv.restrictNormalHom (K₁ := Ω) E ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [habel (AlgEquiv.restrictNormalHom E (a : G F Ω)) (AlgEquiv.restrictNormalHom E (b : G F Ω))]
      group
    have h2 := AlgEquiv.restrictNormal_commutes ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E x
    have h3 : AlgEquiv.restrictNormal ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E = 1 := h1
    rw [← h2, h3]
    rfl
  obtain ⟨F₁, hF₁fin, hF₁ab, hF₁real, hF₁dec, hF₁T⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F A v hv V hVo hcomm T hvT
  obtain ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, hfix, hsub⟩ :=
    hlift F₁ hF₁fin inferInstance (isSolvable_of_comm fun a b => hF₁ab.toIsMulCommutative.is_comm.comm a b) hF₁real hF₁T
  have hkey : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ z ∈ F₁, g z = z) →
      ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g hg hz
    exact (hK g).1 (Subgroup.mem_subgroupOf.1 ((hF₁dec ⟨g, hg⟩).1 ((IntermediateField.mem_fixingSubgroup_iff _ _).2 hz)))
  have hkey2 : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) →
      ∀ z ∈ F₁, g z = z := by
    intro g hg hE
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 ((hF₁dec ⟨g, hg⟩).2 (Subgroup.mem_subgroupOf.2 ((hK g).2 hE)))
  refine ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, ?_, ?_⟩
  · intro g hg
    apply (hfix g).2
    let g' : G F Ω := g.restrictScalars F
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    exact hkey2 g' hg' (fun x => g.commutes x)
  · intro g hg
    have hfixP : ∀ x ∈ maximalRealSubfield M, g (algebraMap M Ω x) = algebraMap M Ω x :=
      fun x hx => g.commutes ⟨x, hx⟩
    have hF1 : ∀ z ∈ F₁, g z = z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hsub z hz
      exact hfixP x hx
    have hFfix : ∀ y : F, g.toRingEquiv (algebraMap F Ω y) = algebraMap F Ω y :=
      fun y => hF1 _ (F₁.algebraMap_mem y)
    let g' : G F Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hFfix
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    have hE : ∀ x : E, g.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := hkey g' hg' hF1
    let g'' : G E Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hE
    exact (hfix g'').2 hF1

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryOneFiniteAdelicOfDetNormOne
section
noncomputable section
namespace GlobalTheory.TwU
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneByOne
variable {R : Type} [CommRing R]

end OneByOne

variable {D : D7}

theorem det_mem_normOne_of_mem_unitaryPoints {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} (hJ : IsUnit J.det)
    {g : GL (Fin n) (AfE D.host.F D.host.E)} (hg : g ∈ UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Matrix.GeneralLinearGroup.det g ∈ U1 (sigD D) := by
  set σR := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have h0 : Formalism.UG.cT σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) * J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) = J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hg
  have h1 := congrArg Matrix.det h0
  simp only [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have e1 : ((g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).map σR).det = σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det := by
    rw [RingHom.map_det]; rfl
  have e2 : (J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).det = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
    rw [RingHom.map_det]; rfl
  rw [e1, e2] at h1
  have hu : IsUnit (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det) := hJ.map _
  have h2 : σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det = 1 := by
    have : (σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det) *
        Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det = 1 * Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
      linear_combination h1
    exact hu.mul_right_cancel this
  show _ = _
  apply Units.ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, conjId, Units.coe_map, Units.val_one,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [mul_comm]
  exact h2

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}


end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldIsoMatrixCongruenceAutomorphismCongruence
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

noncomputable section

namespace GlobalTheory.SeamCong

theorem qOf_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [← (RingOfIntegers.mapRingEquiv s.iE).apply_symm_apply y, mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro hy; exact ⟨_, hy, rfl⟩
    · rintro ⟨z, hz, e⟩
      rw [(RingOfIntegers.mapRingEquiv s.iE).injective e] at hz
      exact hz
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (seamP s P).asIdeal (RingOfIntegers.mapRingEquiv s.iE) hI).toEquiv).symm

theorem intAt_seamP_iff {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (e : X.E) :
    IntAt (seamP s P) (s.iE e) ↔ IntAt P e := by
  have hc : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv s.iE y) = s.iE (algebraMap (𝓞 X.E) X.E y) :=
    fun y => rfl
  constructor
  · rintro ⟨r, c, hc', h⟩
    refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
    · rw [← mem_seamP s, RingEquiv.apply_symm_apply]; exact hc'
    · apply s.iE.injective
      rw [map_mul, ← hc, ← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact h
  · rintro ⟨r, c, hc', h⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, RingOfIntegers.mapRingEquiv s.iE c, ?_, ?_⟩
    · rw [mem_seamP s]; exact hc'
    · rw [hc, hc, ← map_mul, h]

theorem cong_seam {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (g : Sp X.E N ≃ₗ[X.E] Sp X.E N)
    (h : ∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) :
    ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) := by
  intro s' l
  have h1 := h l s'
  have hM : ((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [← intAt_seamP_iff s P]
  have e : s.iE (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) =
      (((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) l s' := by
    rw [hM, qOf_seamP, Matrix.sub_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, map_mul, map_inv₀, map_pow,
      map_natCast, map_sub, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [e]
  exact h1

end GlobalTheory.SeamCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
section
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
open Matrix

namespace GlobalTheory.RatInt

theorem mem_range_of_iA_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a : E) (ha : iA F E a ∈ Formalism.L2.Herm.intAf F E) : a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hmem : (fun _ => a : Fin 1 → E) ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    have h2 : (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := Submodule.smul_mem _ (⟨_, ha⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)
    rw [map_one, mul_one]
  rw [Formalism.UG.P.global_lattice_one_holds F E (Fin 1) Λ hfin hspan] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem intAt_of_intAtA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  intro F E _ _ _ _ _ P x ⟨s, hs, hm⟩
  rw [← map_mul] at hm
  obtain ⟨r, hr⟩ := mem_range_of_iA_mem (F := F) _ hm
  exact ⟨r, s, hs, hr.symm⟩

end GlobalTheory.RatInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatumStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  first | exact @GlobalTheory.Mem.Col2.xiOver_eq_XiTop | exact GlobalTheory.Mem.Col2.xiOver_eq_XiTop | (intros; apply GlobalTheory.Mem.Col2.xiOver_eq_XiTop <;> assumption)
end

