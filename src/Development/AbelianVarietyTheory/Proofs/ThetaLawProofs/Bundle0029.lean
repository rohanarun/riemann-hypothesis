module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsSpanTwistedOfIndepSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackSectionsSpanTwisted_of_indep_span : ∀ (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), L.IsLB → (∀ W : T.Opens, GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W) → GlobalTheory.RelBasis.BoxSpan b p₁ p₂ := by
  first | exact @GlobalTheory.RelBasis.boxSpan_of_indep_span | exact GlobalTheory.RelBasis.boxSpan_of_indep_span | (intros; apply GlobalTheory.RelBasis.boxSpan_of_indep_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open ReciprocityTheory.PTheta Matrix

private theorem levelTheta_one_zero {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : GlobalTheory.levelTheta a b 1 τ 0 z = theta a b z τ := by
  unfold GlobalTheory.levelTheta
  have e1 : ((fun i => ((0 : Fin g → ℤ) i : ℝ) / ((1 : ℕ) : ℝ)) + a) = a := by
    funext i; simp
  rw [e1]
  simp

theorem differentiableOn_thetaChar_comp {g : ℕ} {a b : Fin g → ℂ} (h : charHalf g a b)
    {w : (Fin g → Fin g → ℂ) → Fin g → ℂ} (hw : Differentiable ℂ w) :
    DifferentiableOn ℂ (fun p => thetaChar (per p) a b (w p)) (Key.phDom g) := by
  obtain ⟨ha, hb⟩ := h
  have hF := GlobalTheory.KeyKa.LevelBasis.holFam_levelTheta (fun i => (a i).re) (fun i => (b i).re) Nat.one_pos 0
  unfold GlobalTheory.KeyKa.HolFam at hF
  simp only [levelTheta_one_zero] at hF
  have hm : Differentiable ℂ (fun p : Fin g → Fin g → ℂ => (p, w p)) := by fun_prop
  refine (hF.comp hm.differentiableOn (fun p hp => ⟨hp, Set.mem_univ _⟩)).congr (fun p _ => ?_)
  rw [GlobalTheory.TorusAlg.thetaChar_eq_theta _ ha hb]
  rfl

theorem differentiable_per_apply {g : ℕ} (i j : Fin g) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => per p i j) := by
  simp only [GlobalTheory.KeyKa.per, ReciprocityTheory.ChartRestriction.G.Key.phSym, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

theorem differentiable_lat {g : ℕ} (k n : Fin g → ℤ) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) k n) := by
  rw [differentiable_pi]
  intro i
  have hp := differentiable_per_apply (g := g)
  simp only [lat, Pi.add_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem differentiable_tors {g : ℕ} (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => tors (per p) al m k n r) := by
  have hl : ∀ c, Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) (k c) (n c)) :=
    fun c => differentiable_lat (k c) (n c)
  unfold tors
  exact (Differentiable.fun_sum fun c _ => (hl c).const_smul (al r c)).const_smul ((m : ℂ)⁻¹)

theorem level_one_and_holomorphic : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  intro g a b h
  refine ⟨fun p hp => ?_, fun al m k n y => ?_, fun k n z => ?_⟩
  · have hτ : per p ∈ SiegelH (Fin g) := hp
    obtain ⟨ha, hb⟩ := h
    have e := GlobalTheory.KeyKa.LevelBasis.isLevel_iff (per p) (fun i => (a i).re) (fun i => (b i).re) 1
      (thetaChar (per p) a b)
    rw [GlobalTheory.TorusAlg.ofRealVec_re ha, GlobalTheory.TorusAlg.ofRealVec_re hb] at e
    rw [e, (GlobalTheory.TorusAlg.thetaChar_level hτ.1 hτ.2 ha hb).2.1]
    exact Submodule.mem_span_singleton_self _
  · unfold simTheta
    have hθ : ∀ r, DifferentiableOn ℂ
        (fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r)) (Key.phDom g) :=
      fun r => differentiableOn_thetaChar_comp h
        ((differentiable_const _).add (differentiable_tors al m k n r))
    have hprod : DifferentiableOn ℂ
        (∏ r, fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r))
        (Key.phDom g) :=
      Finset.prod_induction _ (fun F => DifferentiableOn ℂ F (Key.phDom g))
        (fun _ _ h1 h2 => h1.mul h2) (differentiableOn_const 1) (fun r _ => hθ r)
    rw [Finset.prod_fn] at hprod
    exact hprod.mul (differentiableOn_const _)
  · have hp := differentiable_per_apply (g := g)
    simp only [aut, Matrix.mulVec, dotProduct]
    fun_prop

end GlobalTheory.SimilTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta.Frame
open Matrix

private lemma add_lat_eq_add_mulVec_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ)
    (z : Fin g → ℂ) :
    z + lat τ k n = z + τ *ᵥ ReciprocityTheory.PTheta.ofIntVec n + ReciprocityTheory.PTheta.ofIntVec k := by
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  rw [hk, hn, lat]
  abel

private lemma autFactor_re_eq_aut_of_half_characteristics {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    ReciprocityTheory.PTheta.autFactor (fun i => (a i).re) (fun i => (b i).re) τ n k z =
      aut τ a b k n z := by
  rw [ReciprocityTheory.PTheta.autFactor, TorusAlg.ofRealVec_re ha, TorusAlg.ofRealVec_re hb]
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  simp only [aut, ReciprocityTheory.PTheta.eC, hk, hn, ← Complex.exp_add]
  congr 1
  ring

theorem thetaChar_law {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    Differentiable ℂ (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 ∧
      ∀ k n z, thetaChar τ a b (z + lat τ k n) = aut τ a b k n z * thetaChar τ a b z := by
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨hne, hspan, -⟩ := TorusAlg.thetaChar_level hs hp ha hb
  have hmem : thetaChar τ a b ∈
      thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar_iff_autFactor] at hmem
  refine ⟨hmem.1, hne, fun k n z => ?_⟩
  have hper := hmem.2 n k z
  rw [pow_one] at hper
  rw [add_lat_eq_add_mulVec_add, hper, autFactor_re_eq_aut_of_half_characteristics ha hb]

theorem eq_zero_of_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hDz
  have hθa : AnalyticOnNhd ℂ θ Set.univ :=
    SCV.analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn
  have hin : ∀ᶠ w in nhds z, w ∈ S := hS.mem_nhds hz
  have hnear : ∀ᶠ w in nhds z, w ∈ S ∧ D w ≠ 0 :=
    hin.and ((hD.continuousAt (hS.mem_nhds hz)).eventually_ne hDz)
  have hθz : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hnear] with w hw
    rcases mul_eq_zero.1 (h w hw.1) with h' | h'
    · exact h'
    · exact absurd h' hw.2
  have hall := hθa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hθz
  exact h0 (funext fun w => hall (Set.mem_univ w))

theorem frame_eq_aut_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  intro g x h u τ a b hab hw k n i z hz
  obtain ⟨hs, hp, hΛ, -, hth, -⟩ := hw
  have hlaw := thetaChar_law hs hp hab
  obtain ⟨ha, hb⟩ := hab
  have hlatΛ : lat τ k n ∈ u.Λ := (hΛ _).2 ⟨k, n, rfl⟩
  have hex : ∀ w, u.ex (w + lat τ k n) = u.ex w := fun w =>
    CubeValues.ex_add_period u w _ hlatΛ
  let S : Set (Fin g → ℂ) := {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i}
  have hSo : IsOpen S := (u.hol (x.P.L.U i) 0).1
  have hfr : ContinuousOn (u.fr i) S := (u.fr_hol i).continuousOn
  have hfr' : ContinuousOn (fun w => u.fr i (w + lat τ k n)) S := by
    refine hfr.comp (continuous_id.add continuous_const).continuousOn fun w hw => ?_
    show ⊤ ≤ (u.ex (w + lat τ k n)).left ⁻¹ᵁ x.P.L.U i
    rw [hex]
    exact hw
  have haut : Continuous fun w => aut τ a b k n w := by
    unfold aut
    simp only [dotProduct]
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - aut τ a b k n w * u.fr i (w + lat τ k n)) S :=
    hfr.sub (haut.continuousOn.mul hfr')
  refine sub_eq_zero.1 (eq_zero_of_mul_eq_zero hlaw.1 hlaw.2.1 hSo hD (fun w hwS => ?_) hz)
  by_cases hθ : thetaChar τ a b w = 0
  · rw [hθ, zero_mul]
  · have hf := TorusAlg.frame_eq_autFactor_mul u x.th hs ha hb hΛ hth n k i w hwS hθ
    rw [autFactor_re_eq_aut_of_half_characteristics ha hb, ← add_lat_eq_add_mulVec_add] at hf
    rw [← hf, sub_self, mul_zero]

end GlobalTheory.SimilTheta.Frame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosLiftOfIsAdicComplete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.HenselZero
open GlobalTheory.KeyKa.EtBaseChange

section Via
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem map_mem_nonzeroLocus_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : y ∈ Out.nonzeroLocus s') : φ y ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨k, hk⟩ := exists_chart x.P.isLB (φ y)
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hV : y ∈ (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i := ⟨mem_pull.2 hk, x'.P.A.left.basicOpen_le _ hi⟩
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg x'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((Units.isUnit (w.s (fun _ => k, i))).pow l)).ge hV
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hV, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)).le h1).2⟩

theorem exists_gs_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (c : x.P.L.ι) (c' : x'.P.L.ι) (h : φ y ∈ x.P.L.U c) (h' : y ∈ x'.P.L.U c') :
    ∃ u, IsUnit u ∧ gs φ y (x.P.L.U c) (s.f c) = u * gs (𝟙 _) y (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hV : (𝟙 x'.P.A.left : _ ⟶ _) y ∈ (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' := ⟨mem_pull.2 h, h'⟩
  have e := congrArg (gs (𝟙 _) y _) (hs (fun _ => c) c' hle)
  have e₁ := (gs_res (𝟙 _) y hle hV ((φ.app _).hom (s.f c))).trans (gs_pull (𝟙 _) φ y _ h (s.f c))
  rw [Category.id_comp] at e₁
  refine ⟨_, ?_, e₁.symm.trans (e.trans ((gs_mul _ _ _ hV _ _).trans
    (congrArg (_ * ·) (gs_res (𝟙 _) y inf_le_right hV _))))⟩
  rw [gs_eq _ _ _ hV]
  exact (((Units.isUnit (w.s (fun _ => c, c'))).pow l).map _).map _

end Via

theorem exists_lift_point {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {x : KeyIn O} {xk : KeyIn (IsLocalRing.ResidueField O)} {φ w}
    {n : ℕ} (hg : xk.P.g = x.P.g) {s : Fin x.P.g → RR x n} {sk : Fin xk.P.g → RR xk n}
    (hvia : KeyVia xk x (IsLocalRing.residue O) φ w) (hs : ∀ i, SecVia xk x φ w (sk i) (s (i.cast hg)))
    (zk : Pt xk) (c' : xk.P.L.ι) (h₁ : ⊤ ≤ zk.left ⁻¹ᵁ xk.P.L.U c')
    (h₂ : ∀ i, valT (T := IsLocalRing.ResidueField O) zk.left (xk.P.L.U c') ((sk i).f c') = 0)
    (h₃ : IsUnit (_root_.GlobalTheory.KeyKa.jac xk sk zk c')) :
    ∃ (z : Pt x) (c : x.P.L.ι), spMap (IsLocalRing.residue O) ≫ z.left = zk.left ≫ φ ∧ ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧
      (∀ i, valT (T := O) z.left (x.P.L.U c) ((s i).f c) = 0) ∧ IsUnit (_root_.GlobalTheory.KeyKa.jac x s z c) ∧
      ∀ (y : x.P.A.left) (pt : Sp (IsLocalRing.ResidueField O)), y ⤳ φ (zk.left pt) →
        (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ r : Sp O, z.left r = y := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := hvia
  have := x.P.isAb.smooth
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hpt : ∀ r : Sp (IsLocalRing.ResidueField O), r = pt := fun r =>
    Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField O)) _ _
  obtain ⟨c, hc⟩ := exists_chart x.P.isLB (φ (zk.left pt))
  have hc' : zk.left pt ∈ xk.P.L.U c' := h₁ (x := pt) trivial
  have hφ : ⊤ ≤ (zk.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun r _ => by
    obtain rfl := hpt r
    exact hc
  have hW := le_inf_pull (T := IsLocalRing.ResidueField O) zk.left c c' hφ h₁
  let u := Units.map (valH (T := IsLocalRing.ResidueField O) zk.left _ hW).toMonoidHom (w.s (fun _ => c, c'))
  have hu : valT (T := IsLocalRing.ResidueField O) zk.left ((x.P.L.pull φ).U (fun _ => c) ⊓ xk.P.L.U c')
      (w.s (fun _ => c, c')).val = u := valT_eq _ _ hW _
  have hd : (Matrix.of fun i k => (valT (T := DualNumber (IsLocalRing.ResidueField O))
      (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) (x.P.L.U c) ((s (i.cast hg)).f c)).snd).det ≠ 0 := by
    refine fun h => mul_ne_zero (pow_ne_zero (Fintype.card (Fin xk.P.g)) (pow_ne_zero n u.ne_zero)) h₃.ne_zero
      ((Matrix.det_smul _ _).symm.trans (Eq.trans ?_ h))
    congr 1
    ext i k
    have l₂ := translate_le zk (xk.v k) (xk.basis.1 _) h₁
    have l₃ : ⊤ ≤ (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c :=
      translate_le zk (xk.v k) (xk.basis.1 _) (U := φ ⁻¹ᵁ x.P.L.U c) hφ
    have e := valT_via (T := DualNumber (IsLocalRing.ResidueField O)) (hs i) _ c c' l₃ l₂
    refine Eq.symm ((congrArg TrivSqZeroExt.snd e).trans ?_)
    refine (snd_pow_mul _ _ _ ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) h₁ _).trans (h₂ i))).trans ?_
    exact congrArg (· ^ n * _) ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) hW _).trans hu)
  obtain ⟨z₀, hz₁, hz₂, hz₃, hz₄⟩ := exists_section_of_transversal hp.1 zk.left (Over.w zk) pt hc
    (fun i : Fin xk.P.g => (s (i.cast hg)).f c)
    (fun i => (valT_via (T := IsLocalRing.ResidueField O) (hs i) zk.left c c' hφ h₁).trans
      (mul_eq_zero_of_right _ (h₂ i)))
    (by
      rw [← (jac_ne_zero_iff_span_eq_maximalIdeal _ xk n sk zk c' pt h₁ h₂).1 h₃.ne_zero]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨v, hv, e⟩ := exists_gs_via (hs i) (zk.left pt) c c' hc hc'
      exact (Ideal.unit_mul_mem_iff_mem _ hv).1 (Ideal.subset_span ⟨i, e⟩))
    (fun k => ((toUnit (epsR _) ≫ zk) * xk.v k).left)
    (fun k => fst_comp_translate zk (xk.v k) (xk.basis.1 _)) (fun k => Over.w ((toUnit (epsR _) ≫ zk) * xk.v k)) hd
  let z : Pt x := Over.homMk z₀ hz₁
  have hz : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := (Scheme.preimage_eq_top_of_closedPoint_mem z₀ (by
    rw [← IsLocalRing.comap_closedPoint (IsLocalRing.residue O)]
    exact (congrArg (fun g => g pt ∈ x.P.L.U c) hz₂).ge hc)).ge
  refine ⟨z, c, hz₂, hz, fun i => hz₃ (i.cast hg.symm), ?_, fun y r hy hy' => ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    refine fun h => hd (Eq.trans ?_ h)
    unfold _root_.GlobalTheory.KeyKa.jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg)]
    congr 1
    ext i k
    have e := translate_comp hp F hF₁ z zk hz₂.symm (x.v (k.cast hg)) (xk.v k) (hv k)
    have l₁ := translate_le z (x.v (k.cast hg)) (x.basis.1 _) hz
    have e₂ := (congrArg (fun q => valT (T := DualNumber (IsLocalRing.ResidueField O)) q (x.P.L.U c)
      ((s (i.cast hg)).f c)) e).trans (valT_spMap F _ l₁ _)
    exact (congrArg TrivSqZeroExt.snd e₂).trans (snd_map _ F hF₁ hF₂ _)
  · obtain rfl := hpt r
    exact hz₄ y hy fun i h => hy' (i.cast hg) (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)

end GlobalTheory.HenselZero


open GlobalTheory.HenselZero in
theorem GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (xk : KeyIn (IsLocalRing.ResidueField O)) φ w (n d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), KeyVia xk x (IsLocalRing.residue O) φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro O _ _ _ _ x xk φ w n d hg s sk zk chk hvia hs ⟨h₁, h₂, h₃, h₄, h₅⟩
  choose z ch hz₀ hz₁ hz₂ hz₃ hz₄ using fun a => exists_lift_point hg hvia hs (zk a) (chk a) (h₁ a) (h₂ a) (h₃ a)
  obtain ⟨_, _, _, ⟨hp, -⟩, -⟩ := hvia
  have := x.P.isAb.proper
  have := isClosedImmersion_fibre hp
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hcp : spMap (IsLocalRing.residue O) pt = IsLocalRing.closedPoint O :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have hw : ∀ a, (z a).left ≫ x.P.A.hom = 𝟙 (Sp O) := fun a => Over.w (z a)
  have hzc : ∀ a, (z a).left (IsLocalRing.closedPoint O) = φ ((zk a).left pt) := fun a =>
    (congrArg (z a).left hcp).symm.trans (congrArg (fun g => g pt) (hz₀ a))
  refine ⟨z, ch, hz₁, hz₂, hz₃, fun a a' h r e => h₄ a a' h pt (φ.isClosedEmbedding.injective ?_), fun y hy => ?_⟩
  · have : IsClosedImmersion ((z a').left ≫ x.P.A.hom) := by
      rw [hw]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp O) : Sp O ⟶ Sp O))
    have := IsClosedImmersion.of_comp (z a').left x.P.A.hom
    obtain ⟨r', hr'⟩ := ((IsLocalRing.specializes_closedPoint r).map (z a).left.continuous).mem_closed
      (z a').left.isClosedEmbedding.isClosed_range ⟨r, e.symm⟩
    have e₁ : r' = IsLocalRing.closedPoint O :=
      (congrArg (fun g => g r') (hw a')).symm.trans ((congrArg x.P.A.hom hr').trans
        (congrArg (fun g => g (IsLocalRing.closedPoint O)) (hw a)))
    rw [← hzc, ← hzc, ← hr', e₁]
  · obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (x.P.A.hom y)).mem_closed
      (x.P.A.hom.isClosedMap _ (isClosed_closure (s := {y}))) ⟨y, subset_closure rfl, rfl⟩
    have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
    obtain ⟨y', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hp y₀ pt (e.trans hcp.symm)
    obtain ⟨a, r, rfl⟩ := h₅ y' fun i h => hy (i.cast hg)
      (hsp.mem_open (Out.nonzeroLocus _).isOpen (map_mem_nonzeroLocus_via (hs i) y' h))
    exact ⟨a, hz₄ a y r hsp hy⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transversal_zeros_of_jacobian_ne_zero_domain : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, _root_.GlobalTheory.KeyKa.jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  first | exact @GlobalTheory.KeyKa.etZ_of_jac_ne_zero | exact GlobalTheory.KeyKa.etZ_of_jac_ne_zero | (intros; apply GlobalTheory.KeyKa.etZ_of_jac_ne_zero <;> assumption)
end

