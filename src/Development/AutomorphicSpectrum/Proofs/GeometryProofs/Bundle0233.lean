module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0232
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicFrame

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have comp_eq_of_algClosedAt {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
      (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
      (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
      (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
      (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
    obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
    obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
    obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
    let : Algebra c.F C.R := C.R.algebra
    have hCZ : C.Z = Z := by
      by_contra hne
      let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
      rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
      let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
      let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
      have he : spMap C.R.val.toRingHom sC = η :=
        PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
      have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
        have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
        rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
          Scheme.Hom.comp_apply, he] at hgen
        exact hgen
      have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
        (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
      exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
        (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη
    have : Algebra.Smooth c.F C.R := C.sm
    have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
        (t : Ix D → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
        ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
      rintro k x ⟨φ, y', t', hy', ht'⟩
      obtain ⟨w, hw⟩ := hL.bc _ _ φ z
      exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
        hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
    obtain ⟨f, hf⟩ := hread k x hk
    obtain ⟨f', hf'⟩ := hread k' x' hk'
    refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
    have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
      rw [hCZ]; exact hac
    exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpOnto

theorem isHolTo_slice {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {B : Set V} {b : V} (hb : b ∈ B) {c : V × V' → (Sp ℂ ⟶ X)}
    (h : IsHolTo (B ×ˢ Set.univ) c) : IsHolTo Set.univ (fun z => c (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : V' => (b, z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, hb, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩

theorem isHolTo_const_param {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {c : V' → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ c) :
    IsHolTo (Set.univ ×ˢ Set.univ) (fun p : V × V' => c p.2) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage (continuous_snd (X := V) (Y := V'))
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_self, true_and] using h3
  · exact h2.comp differentiable_snd.differentiableOn fun z hz => ⟨trivial, hz.2⟩

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem isHolTo_ex (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z => (e.ex b z).left) :=
  isHolTo_slice (V := Fin n → ℂ) (V' := Fin g → ℂ) (X := G.left) (b := b) (B := B)
    (c := fun bz => (e.ex bz.1 bz.2).left) hb e.hol

def atPoint (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    FamExp G M (Set.univ : Set (Fin 0 → ℂ)) (fun _ => ψ b) where
  ex _ z := e.ex b z
  add _ _ z w := e.add b hb z w
  hol := isHolTo_const_param (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (e.ex b z).left) (isHolTo_ex e hb)
  diff _ _ a := e.diff b hb a
  log b₀ _ := by
    obtain ⟨V, N, f, L, h1, h2, h3, h4⟩ := e.log b hb
    have hφ : Continuous (fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) := by fun_prop
    have hφ' : Continuous (fun p : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, p.2)) := by fun_prop
    refine ⟨V, N, f, fun p => L (b, p.2), h1, ?_, ?_, ?_⟩
    · exact AnalyticAt.comp (f := fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) h2
        (analyticAt_const.prod analyticAt_snd)
    · exact (hφ'.tendsto (b₀, 0)).eventually h3
    · exact (hφ.tendsto (b₀, _)).eventually h4

end GlobalTheory.CompanionTheory.Ar.Flat.ExpOnto

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ExpOnto

theorem famExp_ex_surjective : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Function.Surjective (e.ex b) := by
  intro R _ G _ _ g n M B ψ e hG b hb
  have hc : IsHolTo (Metric.ball (0 : ℂ) 1) (fun _ : ℂ => spMap (ψ b)) :=
    fun U f => ⟨Metric.isOpen_ball.inter isOpen_const, differentiableOn_const _⟩
  obtain ⟨m, ρ, u, hρ, -, -, hu, -⟩ := GlobalTheory.RelExp.exists_exp_along_disc (Sp R) G (fun _ => spMap (ψ b)) 1 hG one_pos hc
  obtain ⟨hadd, hsurj, hhol, -⟩ := hu 0 (Metric.mem_ball_self hρ)
  obtain ⟨h, -, hh⟩ := exists_linear_lift_of_additive_family R G g 0 M Set.univ (fun _ => ψ b) (atPoint e hb) m Set.univ
    (fun _ z => u 0 z) isOpen_univ subset_rfl (fun _ _ z w => hadd z w)
    (isHolTo_const_param (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (u 0 z).left) hhol)
  intro x
  obtain ⟨z, rfl⟩ := hsurj x
  exact ⟨h 0 z, (hh 0 trivial).1 z⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FinAll

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem iotaMulti_coe_eq_det_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {r : ℕ}
    {S : Submodule R M} (c : Module.Basis (Fin r) R S) (v : Fin r → S) :
    exteriorPower.ιMulti R r (fun i => (v i : M)) =
      c.det v • exteriorPower.ιMulti R r (fun i => (c i : M)) := by
  have h : (exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype =
      c.det.smulRight (exteriorPower.ιMulti R r (fun i => (c i : M))) := by
    refine Module.Basis.ext_alternating c fun i hi => ?_
    let σ : Equiv.Perm (Fin r) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change ((exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype) (c ∘ σ) =
      c.det (c ∘ σ) • exteriorPower.ιMulti R r (fun i => (c i : M))
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
    rfl
  exact DFunLike.congr_fun h v

theorem exists_smul_iotaMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (S : Submodule Ω V) {n : ℕ} (v : Fin n → V)
    (a : ⋀[Ω]^n V) (x : Cpt ξ) (α : Ω) (hα : α ≠ 0) (hv : LinearIndependent Ω v)
    (hS : Submodule.span Ω (Set.range v) = S)
    (h : (L.inter S).wedge n x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ c : Ω, a = c • exteriorPower.ιMulti Ω n v := by
  have hmem : α • a ∈ (L.inter S).wedge n x := by rw [h]; exact Submodule.mem_span_singleton_self _
  have key : ∀ y ∈ (L.inter S).wedge n x, ∃ c : Ω, y = c • exteriorPower.ιMulti Ω n v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      let e : Module.Basis (Fin n) Ω (Submodule.span Ω (Set.range v)) := Module.Basis.span hv
      let b' : Fin n → Submodule.span Ω (Set.range v) := fun i => ⟨b i, by rw [hS]; exact (hb i).2⟩
      refine ⟨e.det b', ?_⟩
      have h1 := iotaMulti_coe_eq_det_smul e b'
      have h2 : (fun i => ((e i : Submodule.span Ω (Set.range v)) : V)) = v := by
        funext i; show ((Module.Basis.span hv i : Submodule.span Ω (Set.range v)) : V) = v i
        rw [Module.Basis.span_apply]
      rw [h2] at h1
      exact h1
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hz
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      exact ⟨(r : Ω) * c, by rw [Subring.smul_def, smul_smul]⟩
  obtain ⟨c, hc⟩ := key _ hmem
  refine ⟨α⁻¹ * c, ?_⟩
  rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hα, one_smul]

theorem norm_le_one_of_isIntegral (p : Nat.Primes) (R : Type) [CommRing R] (κ : R →+* ℂ_[p]) (x : R)
    (hx : IsIntegral ℤ x) : ‖κ x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (κ x) := by
    convert map_isIntegral_int κ hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (κ x) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖κ x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem mem_or_inv_mem {F : Type} [Field F] {O : Type} [CommRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) (x : F) : x ∈ β.range ∨ x⁻¹ ∈ β.range := by
  by_cases hx : ‖κ x‖ ≤ 1
  · exact Or.inl ((h x).1 hx)
  · right
    apply (h _).1
    rw [map_inv₀, norm_inv]
    push_neg at hx
    exact inv_le_one_of_one_le₀ hx.le

theorem exists_frac {F : Type} [Field F] {O : Type} [CommRing O] [IsDomain O] (β : O →+* F)
    (hr : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) (x : F) : ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
  rcases hr x with ⟨a, rfl⟩ | ⟨b, hb⟩
  · exact ⟨a, 1, one_ne_zero, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
    · refine ⟨1, b, ?_, ?_⟩
      · rintro rfl; simp at hb; exact hx hb.symm
      · rw [hb, mul_inv_cancel₀ hx, map_one]

theorem norm_natCast_prime (p : Nat.Primes) : ‖(((p : ℕ) : ℂ_[p]))‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[(p : ℕ)] ℂ_[(p : ℕ)]) (p : ℕ), norm_algebraMap', Padic.norm_p]

theorem dvd_prime {F : Type} [Field F] [CharZero F] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) {ϖ : O} (hϖ : Irreducible ϖ) :
    ϖ ∣ ((p : ℕ) : O) := by
  have hnu : ¬ IsUnit ((p : ℕ) : O) := by
    rintro ⟨u, hu⟩
    have hmem : ((p : ℕ) : F)⁻¹ ∈ β.range := by
      refine ⟨(u⁻¹ : Oˣ), ?_⟩
      have h1 : β (u : O) * β ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hu, map_natCast] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hle := (h _).2 hmem
    rw [map_inv₀, map_natCast, norm_inv, norm_natCast_prime, inv_inv] at hle
    have h1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    linarith
  have hm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

theorem constClosed_of_isGeom {F : Type} [Field F] {Ω : Type} [Field Ω] {O : Type} [CommRing O]
    (β : O →+* F) (inc : F →+* Ω) (hβ : Function.Injective β)
    (hfr : ∀ x : F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a)
    (hg : ∀ x : Ω, (∃ f : Polynomial F, f ≠ 0 ∧ f.eval₂ inc x = 0) → x ∈ Set.range inc) :
    @ConstClosed O Ω _ _ (inc.comp β).toAlgebra := by
  letI : Algebra O Ω := (inc.comp β).toAlgebra
  intro a ha
  obtain ⟨f, hf0, hfa⟩ := ha
  obtain ⟨y, rfl⟩ := hg a ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
    rw [Polynomial.eval₂_map]; exact hfa⟩
  obtain ⟨x', y', hy', e⟩ := hfr y
  refine ⟨x', y', hy', ?_⟩
  show inc y * inc (β y') = inc (β x')
  rw [← map_mul, e]

theorem exists_basis_of_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) {n : ℕ} (h : Module.finrank K S = n) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  have hli : LinearIndependent K (S.subtype ∘ b) := b.linearIndependent.map' S.subtype S.ker_subtype
  refine ⟨S.subtype ∘ b, hli, ?_⟩
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem finConstAll : FinConstAll := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ p κ φ hτ hβ hnorm hsplit hN3 hgeom hflat hline
  have hr := mem_or_inv_mem β κ hnorm
  have hfr := exists_frac β hr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ ((p : ℕ) : O) := dvd_prime β κ hnorm hϖ
  obtain ⟨hprop, hnormal, hover, hgf, hfd, hrk, hrk'⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts E H D l Xo c O β Y U Z τ hβ hfr hτ
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  haveI := hfd
  haveI := hprop
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  let σ : E →+* Z.Ω := Z.inc.comp (τ.codRestrict c.F.toSubfield (c.conj τ) : E →+* c.F)
  let σ' : E →+* Z.Ω := Z.inc.comp
    ((ComplexEmbedding.conjugate τ).codRestrict c.F.toSubfield (c.conj _) : E →+* c.F)
  have hσ : ∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b) := fun b => rfl
  have hbar : ∀ a : 𝓞 E, σ' (a : E) = σ (H.bar a : 𝓞 E) := by
    intro a
    show Z.inc _ = Z.inc _
    congr 1
    apply Subtype.ext
    show (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have hinv : ∀ a, H.bar (H.bar a) = a := by
    intro a
    apply RingOfIntegers.ext
    apply τ.injective
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, H.bar_eq, IsCMField.complexEmbedding_complexConj,
      Complex.conj_conj]
  have heig : HT.eigSp Z.ρ σ = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) := rfl
  have heig' : HT.eigSp Z.ρ σ' = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) := rfl
  obtain ⟨v, hvli, hvsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ) (heig ▸ hrk)
  obtain ⟨w, hwli, hwsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ') (heig' ▸ hrk')
  obtain ⟨𝓗, hdeg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model E H D l Xo c O β Y U Z τ ϖ (p : ℕ) hϖ p.2 hdvd hβ hr hsplit hN3
  obtain ⟨u, hu, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx.exists_adapted_basis E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar σ σ' D.p D.q v w 𝓗.act_fst 𝓗.act_inr
    hbar hinv hvli hvsp hwli hwsp
  obtain ⟨-, a, b, ⟨ha0, hb0, hco⟩, hrep⟩ := hflat
  let x₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩
  have hx₀ : x₀ ∈ Z.genFib := ⟨Y.jQ (genPt Z.ξ₀), rfl⟩
  obtain ⟨α₁, β₁, hα₁, hβ₁, hA, hB, -⟩ := hco x₀ hx₀
  obtain ⟨α, rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ) v a x₀ α₁ hα₁ hvli hvsp hA
  obtain ⟨κ', rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ') w b x₀ β₁ hβ₁ hwli hwsp hB
  have hκ' : κ' ≠ 0 := fun h => hb0 (by rw [h, zero_smul])
  have hgfe : Z.genFib = genFibre O (Z.ξ₀ ≫ Y.j) := Set.ext fun x => hgf x
  have hline' : IsLineGenOn (Z.M.lat.inter (HT.eigSp Z.ρ σ)) (Z.M.lat.inter (HT.eigSp Z.ρ σ')) D.p D.q
      (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w)
      (genFibre O (Z.ξ₀ ≫ Y.j)) := by
    rw [← hgfe]; exact ⟨ha0, hb0, hco⟩
  have hinjO : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hσrange : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro a
    obtain ⟨o, ho⟩ := (hnorm (tauIn c τ a)).1
      (norm_le_one_of_isIntegral p (𝓞 E) (κ.comp (tauIn c τ)) a (RingOfIntegers.isIntegral a))
    exact ⟨o, by show Z.inc (β o) = Z.inc (tauIn c τ a); rw [ho]⟩
  have hcc : ConstClosed O Z.Ω := constClosed_of_isGeom β Z.inc hβ hfr hgeom
  obtain ⟨M, k, hM, hord⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.COrder.order_on_component Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E Z.V Z.M.lat Z.ρ H.bar D.p D.q 𝓗 σ σ'
    v w u α κ' O Y.s ϖ hϖ hinjO hover Z.gen hnormal hcc hσrange hbar hinv hvli hvsp hwli hwsp hu (hdeg σ) hline'
  exact _root_.GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point E H D l Xo c O β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M k hτ hϖ hβ hnorm hσ hvli hvsp hwli
    (hwsp.trans heig') hu hM hord hκ' hrep hline

end GlobalTheory.CompanionTheory.Ar.Flat.FinAll
end
end

