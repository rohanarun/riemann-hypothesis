module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieFree
public import Development.WeilBound.CoreStatements.AmpleLineBundles.NonemptyLieMetricOfCoordinates
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ZeroSetSpecialFibreConnected

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptStalk

theorem isIntegrallyClosed_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hg : IsCptGen ξ) (q : Cpt ξ) : IsIntegrallyClosed (regAt ξ q) := by
  let e : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
    RingEquiv.ofBijective (genMap ξ q).rangeRestrict
      ⟨fun x y hxy => hg.inj q (congrArg Subtype.val hxy), (genMap ξ q).rangeRestrict_surjective⟩
  haveI := (hn q.1).1
  haveI := (hn q.1).2
  exact IsIntegrallyClosed.of_equiv e

theorem asIdeal_eq_bot {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ)
    {F : Type} [Field F] [NumberField F] (s : X ⟶ Spec (CommRingCat.of (𝓞 F))) (b : 𝓞 F →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom b)) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) :
    (s p.1).asIdeal = ⊥ := by
  letI : Algebra (𝓞 F) Ω := b.toAlgebra
  have hreg := ConstReg.regular_const X Ω ξ (𝓞 F) s hs p
  refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
  by_contra h0
  have hn : Ideal.absNorm (Ideal.span {o}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  have hmem : ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F) ∈ (s p.1).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ho (Ideal.absNorm_mem _)
  have hu := hp ((Ideal.absNorm (Ideal.span {o}) : ℕ) : ℤ) (by exact_mod_cast hn)
  have hu' : unitAt ξ p (algebraMap (𝓞 F) Ω ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F)) := by
    simpa using hu
  exact ((hreg _).2 hg).1 hu' hmem

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
  {i : Ω₀ →+* Ω} {V V' : Type} [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
  {M : LieModel t.G ξ V} {M' : LieModel t'.G ξ' V'} {ρ : 𝓞 E →+* Module.End Ω₀ V}
  {ρ' : 𝓞 E →+* Module.End Ω V'} {j : V →+ V'}


include m in
theorem map_act (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) (a : 𝓞 E) (e : V) :
    j (ρ a e) = ρ' a (j e) := by
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  refine M'.inj (hcanc _ _ ?_)
  rw [hj, hact a e, hact' a (j e), Over.comp_left, Over.comp_left, Category.assoc, m.act a,
    ← Category.assoc (M'.pt (j e)).left]
  exact congrArg (· ≫ _) (hj e).symm


include m in
theorem map_mem_eigSp (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (hsl : ∀ (a : Ω₀) (e : V), j (a • e) = i a • j e) (σ : 𝓞 E →+* Ω₀) {e : V} (he : e ∈ eigSp ρ σ) :
    j e ∈ eigSp ρ' (i.comp σ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← map_act m hact hact' hj, he a, hsl]
  rfl

theorem eigLat_eq_pull [CharZero Ω₀] [CharZero Ω] (cst : c.F →+* Ω₀) (hg : IsCptGen ξ) (hg' : IsCptGen ξ')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hint : ∀ q : Cpt ξ, IsIntegrallyClosed (regAt ξ q)) (hint' : ∀ q : Cpt ξ', IsIntegrallyClosed (regAt ξ' q))
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (s : CMType H ⊕ CMType H) (q : Cpt ξ') (hq : ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) :
    M'.eigLat ρ' ((i.comp cst).comp (labelEmb c s)) q =
      (M.eigLat ρ (cst.comp (labelEmb c s))).pull ξ' f j q := by
  obtain ⟨j₂, hj₂, hsl₂, -, -, hlat₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat E H X t X' t' f m Ω₀ Ω ξ ξ' i V V' M M' hg hg' hd
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  have hjj : j₂ = j := by
    ext e
    exact M'.inj (hcanc _ _ ((hj₂ e).trans (hj e).symm))
  subst hjj
  have hlat := hlat₂
  have hsl := hsl₂
  obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f i hd q
  have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
    hn (by
      have := h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr))
      exact this)
  have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact (fun q _ => hint q)).2 _ hp
  have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' (i.comp cst) M' ρ' hact' (fun q _ => hint' q)).1
  have hle : ∀ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q ≤ M'.lat q ⊓
      (eigSp ρ' ((i.comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
    intro u
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he2 : e ∈ eigSp ρ (cst.comp (labelEmb c u)) := he.2
    have h3 : j₂ e ∈ eigSp ρ' ((i.comp cst).comp (labelEmb c u)) := by
      rw [RingHom.comp_assoc]
      exact map_mem_eigSp m hact hact' hj₂ hsl _ he2
    refine ⟨?_, h3⟩
    show j₂ e ∈ M'.lat q
    rw [hlat]
    exact Submodule.subset_span ⟨h, e, he.1, rfl⟩
  have hall : M'.lat q ≤ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q := by
    rw [hlat]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
      rw [← hsum]
      exact he
    refine Submodule.iSup_induction _ (motive := fun e =>
      j₂ e ∈ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q) he1 (fun u e he => ?_) ?_
      (fun x y hx hy => ?_)
    · exact Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, he, rfl⟩)
    · simp only [map_zero]
      exact zero_mem _
    · simp only [map_add (f := _)]
      exact add_mem hx hy
  refine le_antisymm ?_ (hle s)
  rintro x ⟨hx1, hx2⟩
  exact FlagStep.mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2

end Eig

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)

theorem labelEmb_inl (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

theorem labelEmb_inr (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  change τ.1 ((H.bar a : 𝓞 E) : E) = (ComplexEmbedding.conjugate τ.1) (a : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

end Labels

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 τ i j hT p hp
  obtain ⟨hd, hi, -, hpt⟩ := hT
  have hg' := 𝔐.tie.gen
  have hg := Z.gen
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hq : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p := fun r hr hf =>
    hf (by simpa using hp (r : ℤ) (by exact_mod_cast hr.ne_zero))
  have hcore : ∀ s, 𝔐.V s p = (Z.M.eigLat Z.ρ (Z.inc.comp (labelEmb c s))).pull 𝔐.ξ 𝔐.f j p := by
    intro s
    have h1 : 𝔐.V s p = 𝔐.M.eigLat 𝔐.ρ (𝔐.cst.comp (labelEmb c s)) p :=
      Lat.patch_of_not S _ _ fun r hr => hq r (𝔐.S_prime r hr)
    rw [h1, ← hi]
    exact eigLat_eq_pull c 𝔐.m Z.inc hg hg' hd Z.act 𝔐.act (isIntegrallyClosed_regAt Y.normal hg)
      (isIntegrallyClosed_regAt 𝔐.normal hg') hpt s p hq
  refine ⟨?_, ?_, ?_⟩
  · have hb : (Y.s (𝔐.f p.1)).asIdeal = ⊥ := by
      have := asIdeal_eq_bot hg' (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over hp
      rwa [Scheme.Hom.comp_apply] at this
    refine ⟨⟨𝔐.f p.1, hd.specializes p⟩, ?_, rfl⟩
    show 𝔐.f p.1 ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
    have e : Y.s (𝔐.f p.1) = spMap (algebraMap (𝓞 c.F) c.F) w := by
      refine PrimeSpectrum.ext ?_
      rw [hb]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : algebraMap (𝓞 c.F) c.F o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : algebraMap (𝓞 c.F) c.F o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  · rw [hcore, labelEmb_inl]
    rfl
  · rw [hcore, labelEmb_inr]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidance
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance : Inputs → AvoidStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → CmpSt := by
  intro hIn hAv hRes II hII K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ Ω _ _ y D σ _ S₁ S₂ Re₁ Re₂ β b
    hb₁ hb₂ hAr hβ hβy halg₁ halg₂ hsing w
  obtain ⟨K', _, ι', _, κ, v, y', S, Re, f, g, d, hbl, hyv, hfield, hdeg, ht₁, ht₂, hpull, hiso,
    hsm, hph, hrel⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cmp.BuildK.joint_system hIn hRes K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b
      hb₁ hb₂ hAr hβ hβy halg₁ halg₂ hsing
  have hlim := GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.cmp_one hIn hAv II hII K' ι' (mCoordIdeal y') D σ S Re f g d
    hiso hsm hph hrel w
  have hpos₁ : 0 < S₁.t₀ := (S₁.reg (w 0)).1
  have hpos₂ : 0 < S₂.t₀ := (S₂.reg (w 0)).1
  have hPF : HasPFCoord II := hII.2.2.1
  refine hlim.congr' ?_
  have hmem : Set.Ioc (0 : ℝ) (min S₁.t₀ S₂.t₀) ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (lt_min hpos₁ hpos₂)
  filter_upwards [hmem] with t ht
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.CoordK.side_eq II hPF Re₁ Re Sum.inl hb₁ hbl hyv hfield hdeg
      (fun a t => (hpull a t).1) w t ht.1 (le_trans ht.2 (min_le_left _ _)),
    GlobalTheory.CompanionTheory.Ar.Cmp.CoordK.side_eq II hPF Re₂ Re Sum.inr hb₂ hbl hyv hfield hdeg
      (fun a t => (hpull a t).2) w t ht.1 (le_trans ht.2 (min_le_right _ _))]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EventuallyOneTmulAdicIntegralCoords
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

def lieModelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add (f := _), M.add]
  smul c v := by rw [map_smul, M.smul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieMetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.MetricAny

theorem exists_lieMetric : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), Nonempty (LieMetric M y) := by
  exact @CoverDenseAlt.nonempty_lie_metric_of_coordinates

end GlobalTheory.CompanionTheory.Ar.MetricAny
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_torsion_generator_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModels
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hcpt_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) :=
  @PositivityTheory.HtPt.Hcptgen.hcpt_generic

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem injective_ringOfIntegers_toComplex {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    Function.Injective g := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  have h : Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = RingHom.ker (g.comp (algebraMap ℤ (𝓞 F))) :=
    RingHom.comap_ker _ _
  change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = ⊥
  rw [h, (RingHom.injective_iff_ker_eq_bot _).1]
  have e : g.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [e]
  exact Int.cast_injective

theorem exists_comp_eq_of_ringOfIntegers {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    ∃ g' : F →+* ℂ, g'.comp (algebraMap (𝓞 F) F) = g :=
  ⟨IsFractionRing.lift (injective_ringOfIntegers_toComplex g), by
    ext a
    simp⟩

theorem exists_spMap_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp (𝓞 F))
    (u : Sp ℂ ⟶ X) : ∃ g' : F →+* ℂ, u ≫ s = spMap g' ≫ spMap (algebraMap (𝓞 F) F) := by
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_ringOfIntegers (Spec.preimage (u ≫ s)).hom
  refine ⟨g', ?_⟩
  rw [← spMap_comp, hg']
  exact (Spec.map_preimage (u ≫ s)).symm

theorem polarisedAt_of_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z hz
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have h₁ : (z ≫ 𝔐.f) p ∈ abLocus Y.t.G := by
    have := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (z p)).2 hz
    simpa using this

  obtain ⟨g', hg'⟩ := exists_spMap_of_ringOfIntegers Y.s (z ≫ 𝔐.f)
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift (z ≫ 𝔐.f) (spMap g') hg'
  have hw : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _

  have h₂ : w p ∈ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    show (pullback.fst Y.s _) (w p) ∈ abLocus Y.t.G
    have : (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (w p) = (z ≫ 𝔐.f) p := by
      rw [← hw]; simp
    rw [this]; exact h₁
  have h₃ : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  haveI := Y.jQ_open
  let v : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w h₃
  have hv : v ≫ Y.jQ ≫ pullback.fst _ _ = z ≫ 𝔐.f := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hw]

  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
  have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ pullback.fst _ _) (_ : SABMap t' Y.t q),
      Nonempty (SABMap t' Y.oF.t v) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hv.symm n
  obtain ⟨w₂, g₂, -⟩ := m₃.lin
  obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
  exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isConnected_zeroSet_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) :=
  @PositivityTheory.Xgn.zero_set_special_fibre_connected

end GlobalTheory.CompanionTheory.Ar.Flat
end

