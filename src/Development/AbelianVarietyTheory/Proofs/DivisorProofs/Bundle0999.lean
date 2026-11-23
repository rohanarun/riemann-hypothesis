module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOrbIntOfIsCompactCentConj
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem hasOrbInt_of_isCompact_cent_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsCompact (cent s : Set H) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], IsProperOrbit (cent s) s → ∀ (y : H) (f : H → ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ) := by
  intro H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc
  haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
  obtain ⟨C, hC, h0⟩ := hP _ hc
  have hcont : Continuous (conjFn s f) := hf.comp (by fun_prop)
  have hsupp : HasCompactSupport (conjFn s f) := by
    refine HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_
    by_contra hne
    obtain ⟨t, ht, htx⟩ := h0 x (subset_tsupport f hne)
    exact hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩
  have hint : Integrable (conjFn s f) μ := hcont.integrable_of_hasCompactSupport hsupp
  have e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ := by
    have := integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y
    rw [← this]
    congr 1; ext x; congr 1; group
  rw [e]
  exact hasOrbInt_of_finite hint

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.HeckeBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compInf_eq_infTens (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w z = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem coe_infDiag (k : Eˣ) :
    (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem exists_tensor_adele_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv F E σ hcm
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc, hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

theorem exists_hchar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E,
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

end GlobalTheory.HeckeBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosets
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CosetFin

variable {H : Type} [Group H]

theorem finite_mk_mul (A K : Subgroup H) (x : H) (h : (K.map (MulAut.conj x).toMonoidHom).relIndex A ≠ 0) :
    {q : H ⧸ K | ∃ a ∈ A, q = (QuotientGroup.mk (a * x) : H ⧸ K)}.Finite := by
  set S := (K.map (MulAut.conj x).toMonoidHom).subgroupOf A
  haveI : S.FiniteIndex := ⟨h⟩
  haveI : Finite (A ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_range (fun t : A ⧸ S => (QuotientGroup.mk ((t.out : H) * x) : H ⧸ K))).subset ?_
  rintro q ⟨a, ha, rfl⟩
  refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ S), ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul S (⟨a, ha⟩ : A)
  simp only
  rw [hu]
  have hu2 : ((u : A) : H) ∈ K.map (MulAut.conj x).toMonoidHom := u.2
  obtain ⟨k, hk, hke⟩ := hu2
  rw [QuotientGroup.eq]
  have : ((u : A) : H) = x * k * x⁻¹ := by rw [← hke]; rfl
  simp only [Subgroup.coe_mul, this]
  have e : (a * (x * k * x⁻¹) * x)⁻¹ * (a * x) = k⁻¹ := by group
  rw [e]; exact K.inv_mem hk

theorem finite_mk_dcoset (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (s : H) :
    {q : H ⧸ K | ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, q = (QuotientGroup.mk (k₁ * s * k₂) : H ⧸ K)}.Finite := by
  set T := K.subgroupOf K₀
  haveI : T.FiniteIndex := ⟨hc⟩
  haveI : Finite (K₀ ⧸ T) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_iUnion (fun t : K₀ ⧸ T => finite_mk_mul K₀ K (s * (t.out : H)) (hconj _))).subset ?_
  rintro q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨k₂, hk₂⟩ : K₀) : K₀ ⧸ T), k₁, hk₁, ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul T (⟨k₂, hk₂⟩ : K₀)
  rw [hu, QuotientGroup.eq]
  have hu2 : ((u : K₀) : H) ∈ K := u.2
  simp only [Subgroup.coe_mul]
  have e : (k₁ * s * k₂)⁻¹ * (k₁ * (s * (k₂ * ((u : K₀) : H)))) = ((u : K₀) : H) := by group
  rw [e]; exact hu2

theorem finite_mk_support (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (φ : H → ℂ) (S : Finset H)
    (hS : ∀ g, φ g ≠ 0 → ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂) :
    {q : H ⧸ K | ∃ g, φ g ≠ 0 ∧ q = (QuotientGroup.mk g : H ⧸ K)}.Finite := by
  refine (S.finite_toSet.biUnion fun s _ => finite_mk_dcoset K₀ K hc hconj s).subset ?_
  rintro q ⟨g, hg, rfl⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem relIndex_ne_zero_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (y : G) :
    IsOpen ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  have e : ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) = (fun g => y⁻¹ * g * y) ⁻¹' (U : Set G) := by
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : y⁻¹ * ((MulAut.conj y).toMonoidHom k) * y = k := by
        show y⁻¹ * (y * k * y⁻¹) * y = k; group
      rw [this]; exact hk
    · intro h
      refine ⟨_, h, ?_⟩
      show y * (y⁻¹ * g * y) * y⁻¹ = g; group
  rw [e]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.CosetFin

namespace GlobalTheory.CosetFin

theorem commensurable_map_conj {G : Type} [Group G] {A B : Subgroup G} (h : A.Commensurable B) (y : G) :
    (A.map (MulAut.conj y).toMonoidHom).Commensurable (B.map (MulAut.conj y).toMonoidHom) := by
  exact ⟨h.1.map _, h.2.map _⟩

end GlobalTheory.CosetFin


open GlobalTheory.CosetFin in
theorem GlobalTheory.testProd_support_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  intro p _ G L f hf _ K' f' hf' _
  obtain ⟨-, -, -, S, hS⟩ := hf
  obtain ⟨hc', -, -, S', hS'⟩ := hf'

  have hA : {a : G.GAf ⧸ L.K.toSubgroup | ∃ g, f g ≠ 0 ∧ a = (QuotientGroup.mk g : G.GAf ⧸ L.K.toSubgroup)}.Finite := by
    refine finite_mk_support L.K.toSubgroup L.K.toSubgroup ?_ ?_ f S hS
    · rw [Subgroup.relIndex_self]; exact one_ne_zero
    · intro y
      exact relIndex_ne_zero_open_compact _ _ (isOpen_map_conj _ L.K.isOpen y) L.compact

  have hB : {b : Gr G 1 ⧸ K' | ∃ g, f' g ≠ 0 ∧ b = (QuotientGroup.mk g : Gr G 1 ⧸ K')}.Finite := by
    refine finite_mk_support (KHT p G.m G.n 1 G.Fw) K' hc'.1.relIndex_ne_zero ?_ f' S' hS'
    intro y
    have h1 := (GlobalTheory.heckeOperator_integral p G 1 Nat.one_pos).1 y
    exact ((commensurable_map_conj hc' y).trans h1).1.relIndex_ne_zero
  let ψ : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) →
      (G.GAf ⧸ L.K.toSubgroup) × (Gr G 1 ⧸ K') :=
    fun q => ((QuotientGroup.mk q.out.1 : G.GAf ⧸ L.K.toSubgroup), (QuotientGroup.mk q.out.2 : Gr G 1 ⧸ K'))
  have hψ : Function.Injective ψ := by
    intro q r hqr
    simp only [ψ, Prod.mk.injEq, QuotientGroup.eq] at hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
    apply QuotientGroup.eq.2
    exact Subgroup.mem_prod.2 ⟨by simpa using hqr.1, by simpa using hqr.2⟩
  refine ((hA.prod hB).preimage hψ.injOn).subset ?_
  intro q hq
  have h1 : f q.out.1 ≠ 0 := left_ne_zero_of_mul hq
  have h2 : f' q.out.2 ≠ 0 := right_ne_zero_of_mul hq
  exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HvMemOfInert
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.EtaValues

section General

variable {L : Type} [Field L] [NumberField L]

def hv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  ((χ.val v : ℂˣ) : ℂ) * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ))⁻¹ : ℝ) : ℂ)

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 v.ne_bot)

theorem hv_ne_zero (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : hv χ v ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (absNorm_pos v)).ne'))

theorem valTw_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : χ.valTw (1 / 2) v = hv χ v := by
  unfold HChar.valTw hv
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast, Complex.ofReal_neg]


open Classical in
def cnt (a : 𝓞 L) (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 L))).factors

theorem intValuation_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) :
    v.intValuation a = WithZero.exp (-(cnt a v : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_if_neg _ ha]
  rfl

theorem ordF_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) : ordF v (GlobalTheory.Mem.ValAlg.uOf a ha) = cnt a v := by
  show -WithZero.log (v.valuation L (algebraMap (𝓞 L) L a)) = _
  rw [HeightOneSpectrum.valuation_of_algebraMap, intValuation_eq ha]
  simp

theorem cnt_eq_zero {a : 𝓞 L} (ha : a ≠ 0) {v : HeightOneSpectrum (𝓞 L)} (h : a ∉ v.asIdeal) : cnt a v = 0 := by
  have h1 := intValuation_eq ha v
  rw [HeightOneSpectrum.intValuation_eq_one_iff.2 h, ← WithZero.exp_zero, WithZero.exp_inj] at h1
  omega

theorem prod_hv (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) {a : 𝓞 L} (ha : a ≠ 0) (U : Finset (HeightOneSpectrum (𝓞 L)))
    (hU : ∀ v, a ∈ v.asIdeal → v ∈ U) :
    ∏ v ∈ U, hv χ v ^ cnt a v = (∏ i, φ i (algebraMap (𝓞 L) L a))⁻¹ := by
  classical
  have h0 : ∀ v, v ∉ U → cnt a v = 0 := fun v h => cnt_eq_zero ha (mt (hU v) h)
  have hp := GlobalTheory.TypeValues.productRule χ ∅ (fun v _ => hu v) (GlobalTheory.Mem.ValAlg.uOf a ha)
  have e1 : ∀ v, (∏ᶠ (_ : v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 L)))), χ.val v ^ ordF v (GlobalTheory.Mem.ValAlg.uOf a ha)) =
      χ.val v ^ cnt a v := fun v => by
    rw [finprod_eq_if, if_pos (Finset.notMem_empty v), ordF_eq, zpow_natCast]
  simp_rw [e1] at hp
  rw [Finset.prod_empty, mul_one, finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    exact hv' (by simp only [h0 v h, pow_zero]))] at hp
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, hinf, Units.val_one, Units.coe_prod] at hp'
  have hf := Ideal.finprod_heightOneSpectrum_factorization (I := Ideal.span {a}) (by simpa using ha)
  rw [finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    refine hv' ?_
    show v.asIdeal ^ cnt a v = 1
    rw [h0 v h, pow_zero])] at hf
  have hN := GlobalTheory.Mem.ValAlg.absNorm_eq hL φ hφ a
  rw [← hf, map_prod, Nat.cast_prod] at hN
  have hN' : ∏ v ∈ U, Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) ^ cnt a v = ∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ := by
    refine (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      two_ne_zero).1 ?_
    rw [← hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
    show _ = ((Ideal.absNorm (v.asIdeal ^ cnt a v) : ℕ) : ℝ)
    rw [map_pow, Nat.cast_pow]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hp']
  unfold hv
  simp_rw [mul_pow, Finset.prod_mul_distrib, zpow_one, Finset.prod_div_distrib, Units.val_pow_eq_pow_val,
    ← Complex.ofReal_pow, ← Complex.ofReal_prod, inv_pow, Finset.prod_inv_distrib, hN', Complex.ofReal_inv]
  show _ = (∏ i, φ i (algebraMap (𝓞 L) L a)) / ((∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ : ℝ) : ℂ) * _
  ring

theorem hv_mem (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) (M : Subfield ℂ) (hM : ∀ i x, φ i x ∈ M) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v, v ∉ S → hv χ v ∈ M) (P : HeightOneSpectrum (𝓞 L)) : hv χ P ∈ M := by
  classical
  by_cases hP : P ∈ S
  swap
  · exact hS P hP
  obtain ⟨b, hb1, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have haP := ha P hP
  rw [if_pos rfl] at haP
  have ha2 : a ∉ P.asIdeal ^ 2 := fun h => hb2 (by simpa using (P.asIdeal ^ 2).sub_mem h haP)
  have ha1 : a ∈ P.asIdeal := by simpa using P.asIdeal.add_mem (Ideal.pow_le_self two_ne_zero haP) hb1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hc : cnt a P = 1 := by
    have h1 := intValuation_eq ha0 P
    rw [GlobalTheory.TypeValues.intValuation_eq_of_mem ha1 ha2, WithZero.exp_inj] at h1
    omega
  have hfin : {v : HeightOneSpectrum (𝓞 L) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by simpa using ha0)
  have hU : ∀ v, a ∈ v.asIdeal ↔ v ∈ hfin.toFinset := fun v => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h := prod_hv hL φ hφ χ hu hinf ha0 hfin.toFinset fun v => (hU v).1
  rw [← Finset.mul_prod_erase _ _ ((hU P).1 ha1), hc, pow_one] at h
  rw [eq_div_of_mul_eq (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hv_ne_zero χ v)) h]
  refine div_mem (inv_mem (prod_mem fun i _ => hM i _)) (prod_mem fun v hv' => pow_mem (hS v fun hvS => ?_) _)
  obtain ⟨hvP, hva⟩ := Finset.mem_erase.1 hv'
  have h1 := ha v hvS
  rw [if_neg hvP] at h1
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  simpa using v.asIdeal.sub_mem ((hU v).2 hva) (Ideal.pow_le_self two_ne_zero h1)

theorem hv_mem_of_inert {F : Type} [Field F] [NumberField F] [Algebra F L] (χ : HChar L) (hr : χ.ResEta F)
    {v : HeightOneSpectrum (𝓞 L)} (hu : χ.UnrAt v) (ho : ∀ k : Fˣ, ordF v (upF F k) = ordF (v.under (𝓞 F)) k)
    (h1 : ((v.under (𝓞 F)).asIdeal.primesOver (𝓞 L)).ncard = 1)
    (hN : Ideal.absNorm v.asIdeal = Ideal.absNorm (v.under (𝓞 F)).asIdeal ^ 2) (M : Subfield ℂ) : hv χ v ∈ M := by
  have hab : aboveF (L := L) F (v.under (𝓞 F)) = {v} := by
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.1 h1
    have key : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v.under (𝓞 F) → w.asIdeal = Q := fun w hw => by
      have : w.asIdeal ∈ (v.under (𝓞 F)).asIdeal.primesOver (𝓞 L) := ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩
      rwa [hQ] at this
    ext P
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun h => HeightOneSpectrum.ext ((key P h).trans (key v rfl).symm), fun h => by rw [h]; rfl⟩
  have hval : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Kˣ),
      IsUnifAt w (atFin w k) ↔ ordF w k = 1 := by
    intro K _ _ w k
    have h : Valued.v ((atFin w k : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (k : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : K)
    have h0 : w.valuation K (k : K) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    unfold IsUnifAt ordF
    rw [h, ← WithZero.exp_log h0, WithZero.exp_inj, WithZero.log_exp]
    omega
  have hk := (hval _ _).1 (unif_spec (v.under (𝓞 F)))
  have h := hr.1 (v.under (𝓞 F)) (unif (v.under (𝓞 F)))
  rw [HChar.resFin, etaFin, hab, Finset.prod_singleton, MonoidHom.comp_apply, if_pos (Finset.card_singleton _), hk, zpow_one] at h
  have h2 : χ.val v = -1 := (χ.val_eq hu _ ((hval _ _).2 ((ho _).trans hk))).symm.trans h
  unfold hv
  rw [h2, hN, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast, Units.val_neg,
    Units.val_one]
  exact mul_mem (neg_mem (one_mem _)) (inv_mem (natCast_mem _ _))

end General

end GlobalTheory.EtaValues

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.EtaValues

open _root_.Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hv_mem_host (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : Formalism.L2.Host.IsEtaT D.host χ) (T : Finset (Pl D.host.E))
    (hT : ∀ v, Bridge.SplitOff v (T : Set (Pl D.host.E)) → hv χ v ∈ D.what₂.embLL.fieldRange) (P : Pl D.host.E) :
    hv χ P ∈ D.what₂.embLL.fieldRange := by
  classical
  obtain ⟨c, -, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  refine hv_mem hcm.cplx _ hcm.bij χ hχ.unr hχ.inf D.what₂.embLL.fieldRange (fun g x => ⟨D.embE (D.host.sigmaOf g x),
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)⟩) (T ∪ T.image conjPrime₂) (fun v hv' => ?_) P
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) v.asIdeal = v.asIdeal
  · have hm : v.asIdeal ∈ (v.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨v.isPrime, ⟨rfl⟩⟩
    rcases GlobalTheory.EtaEulerProduct.inert_or_split (σ := D.sp.cm.sig)
      ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩ (fun _ => rfl)
      D.sp.cm.cmUnram (v.under (𝓞 D.host.F)) with ⟨-, h1, h2⟩ | ⟨-, -, h2⟩
    · exact hv_mem_of_inert χ hχ.res (hχ.unr v) (ho v) h1 (h2 _ hm).2 _
    · exact absurd hc (h2 _ hm).1
  · exact hT v ⟨hc, fun h => hv' (Finset.mem_union_left _ h), fun w hw h => hv' (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨w, hw, by
        rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v))]
        exact HeightOneSpectrum.ext (Ideal.ext fun a => by rw [mem_conjP, mem_conjP, cO_cO])⟩))⟩

theorem splitOff_mono {D : D7} {v : Pl D.host.E} {S S' : Set (Pl D.host.E)} (h : Bridge.SplitOff v S) (hS : S' ⊆ S) :
    Bridge.SplitOff v S' :=
  ⟨h.1, fun h' => h.2.1 (hS h'), fun w hw => h.2.2 w (hS hw)⟩

end GlobalTheory.EtaValues

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizerStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_at_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), UnrAt χ (splitPrime t) → chrW χ t (unifAt v) = val χ (splitPrime t) := by
  first | exact @GlobalTheory.ChrWUnif.chrW_unifAt | exact GlobalTheory.ChrWUnif.chrW_unifAt | (intros; apply GlobalTheory.ChrWUnif.chrW_unifAt <;> assumption)
end

