module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Columns.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.DoubleCosetMeasures.LatticeCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Dict.Lift

namespace GlobalTheory.Dict.FibreMove

theorem exists_frame_push {X Y : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : LB X}
    {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen)
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L'.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L'.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L'.U j ⊓ L'.U j') →
      fr j z = valAt' (e z) (L'.U j ⊓ L'.U j') (L'.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j}) ∧
      (∀ j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j → fr' j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j') →
        fr' j z = valAt' (e z ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * fr' j' z) ∧
      ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr' a z = wv w (e z) a j * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L' hL'
  have key : ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j →
      wv w (e z) a (ch z) * fr (ch z) z = wv w (e z) a j * fr j z := by
    intro a j z ha hj
    have h0 := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have h2 := valAt'_unit_ne_zero (e z) h0 (L'.g (ch z) j)
    rw [wv_change hw ha ha (hch z) hj, val_g_self _ L hL a ha, fr_g (ch z) j z h0]
    field_simp
  refine ⟨fun a z => wv w (e z) a (ch z) * fr (ch z) z, fun a z₀ hz₀ => ?_, fun a z ha => ?_,
    fun a a' z h => ?_, key⟩
  · have hN := (hol ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) (w.s (fun _ => a, ch z₀)).val)
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, mem_both hz₀ (hch z₀)⟩
    have hsub : ∀ z, ⊤ ≤ e z ⁻¹ᵁ ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) →
        ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a ∧ ⊤ ≤ e z ⁻¹ᵁ L'.U (ch z₀) := fun z hz =>
      ⟨(mem_wchart (e z) L _ _).1 ((top_le_preimage_inf _ _ _).1 hz).1 ⟨⟩, ((top_le_preimage_inf _ _ _).1 hz).2⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => (hsub z hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => wv w (e z) a (ch z₀)) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key a (ch z₀) z (hsub z hz.2).1 (hsub z hz.2).2
  · exact mul_ne_zero (wv_ne w ha (hch z)) (fr_ne _ z (hch z))
  · obtain ⟨ha, ha'⟩ := (top_le_preimage_inf _ _ _).1 h
    simp only []
    rw [wv_change hw ha ha' (hch z) (hch z), val_g_self _ L' hL' _ (hch z)]
    ring

theorem anFib_levR {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c ℂ} (h : levR (gM, gA) y y')
    (A : AnFib X bas idx e x L y) :
    ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧
      ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  obtain ⟨ρ, ν, -, hν, hmv⟩ := h
  obtain ⟨hb, hu, pm, w, hf, hs, hcub, hc⟩ := MoveCalc.frMove_iff_carry.1 hmv
  obtain ⟨hw, hrig, -⟩ := hcub
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_frame_push Xo.univ.t.PP.isLB Xo.univ.t.PP.isLB hw
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hadd : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => by
    simp only [ex, A.ex_add, map_mul]
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := hadd
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := (funext hex).symm ▸ PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        have h1 := FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
        rw [hu]
        exact (funext hex).symm ▸ h1
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun a ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch 0
        have h1 := key a j 0 ha hj
        have h2 := A.fr_0 j hj
        have h3 := val_rig ν.cm Xo.univ.t.PP Xo.univ.t.PP w hrig y.x a j (hex0 ▸ ha) (hex0 ▸ hj)
        have h4 : y.x ≫ ν.cm.e = y'.x := by rw [ν.base]; exact hb.symm
        erw [h4, ← h2, ← hex0] at h3
        exact h1.trans h3.symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv a z ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch z
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h1 := key a j z ha hj
        have h2 := key a j (z + pv X idx x v) (hz ▸ ha) (hz ▸ hj)
        have h3 := A.fr_per v hv j z hj
        simp only [hz] at h2
        rw [h1, h2, h3]
        ring }
  refine ⟨A', fun θ hθ a z pt' hp1 hp2 ha => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have ha' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U a := hex z ▸ ha
    let pt : Sp ℂ ⟶ Gx y.x := pullback.lift (𝟙 _) (A.ex z).left (by
      rw [Category.id_comp]; exact (Over.w (A.ex z)).symm)
    have e₁ : pt ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (A.ex z).left := pullback.lift_snd _ _ _
    have e₂ : pt ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ := pullback.lift_fst _ _ _
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact hp2.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · refine (hp1.trans (hex z)).trans ?_
        rw [← e₁]
        exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm
    have h1 := hθ j z pt e₁ e₂ hj
    have h2 := MoveValues.val_carry hs hc pt (i := a) (j := j)
      (by rw [e₁]; exact (MoveValues.mem_iff ((A.ex z).left ≫ ν.φ) _).2 ha')
      (by rw [e₁]; exact (MoveValues.mem_iff _ _).2 hj)
    refine h2.trans ?_
    rw [e₁]
    refine (congrArg (wv w (A.ex z).left a j * ·) h1).trans ?_
    change _ = θ z * fr a z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key a j z ha' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x ((l.M : E)⁻¹ • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hν.2.1, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.Dict.FibreMove

theorem GlobalTheory.Dict.FibreMove.anFib_levR_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h A => GlobalTheory.Dict.FibreMove.anFib_levR h A
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeFrob

theorem rt_mul_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (a b : GAf L n) (f : GAf L n → W) :
    NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
  funext g; simp [NG.rt, mul_assoc]

theorem exists_ne_zero_of_irrRep {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.SmGL.IrrRep G) :
    ∃ a : σ.V, a ≠ 0 := by
  by_contra hne
  push Not at hne
  have h := σ.irr
  have : Subsingleton σ.V := ⟨fun a b => by rw [hne a, hne b]⟩
  exact (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem mem_iSup_range_locMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  intro L _ _ _ n π s σ i T hTi hTS hT g hg
  set I : Submodule ℂ (GAf L n → π.W) :=
    ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 with hIdef
  have hIS : I ≤ π.S := iSup_le fun T' => by
    rintro _ ⟨a, rfl⟩
    exact T'.2.1 a
  have hsub : NG.IsSubrep π.ρ I := by
    refine ⟨hIS.trans π.irrS.1.le, ?_⟩
    intro h f hf
    obtain ⟨x, y, hx, hy, rfl⟩ := (GlobalTheory.SplitAdelic.main L n s).1 h
    have hcomm := (GlobalTheory.SplitAdelic.main L n s).2.1
    refine Submodule.iSup_induction (motive := fun f => NG.rt L n (x * y) f ∈ I) _ hf ?_ ?_ ?_
    · rintro T' _ ⟨a, rfl⟩
      let T'' : σ.V →ₗ[ℂ] (GAf L n → π.W) := (NG.rt L n y).comp T'.1
      have hT'' : (∀ a, T'' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'' := by
        refine ⟨fun a => π.irrS.1.stable y _ (T'.2.1 a), fun z hz a => ?_⟩
        change NG.rt L n y (T'.1 _) = NG.rt L n z (NG.rt L n y (T'.1 a))
        rw [T'.2.2 z hz a, ← rt_mul_apply, ← rt_mul_apply, (hcomm z y hz hy).eq]
      have key : NG.rt L n (x * y) (T'.1 a) =
          T'' (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) := by
        rw [hT''.2 x hx a, rt_mul_apply]
        rfl
      rw [key]
      exact Submodule.mem_iSup_of_mem ⟨T'', hT''⟩ ⟨_, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro f₁ f₂ h₁ h₂
      rw [map_add]; exact add_mem h₁ h₂
  rcases π.irrS.2.2 I hsub hIS with hbot | htop
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne_zero_of_irrRep σ
    have hmem : T a ∈ I := Submodule.mem_iSup_of_mem ⟨T, hTS, hT⟩ ⟨a, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact ha (hTi (hmem.trans (map_zero T).symm))
  · rw [htop]; exact hg

end GlobalTheory.HeckeFrob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.HQStepBlocks

variable {F : Type} [Field F] {r c : ℕ}

theorem submatrix_eq_fromBlocks (x : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    x.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (bAA x) (bAD x) (bDA x) (bDD x) := by
  ext (i|i) (j|j) <;> simp [bAA, bAD, bDA, bDD]

theorem submatrix_mul' (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    (x * y).submatrix finSumFinEquiv finSumFinEquiv =
      x.submatrix finSumFinEquiv finSumFinEquiv * y.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [Matrix.submatrix_mul_equiv]

theorem blocks_mul (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧
    bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  have h := submatrix_mul' x y
  rw [submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, submatrix_eq_fromBlocks,
    fromBlocks_multiply, fromBlocks_inj] at h
  exact h

theorem det_eq_of_bDA_eq_zero (x : Matrix (Fin (r + c)) (Fin (r + c)) F) (hx : bDA x = 0) :
    x.det = (bAA x).det * (bDD x).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv x, submatrix_eq_fromBlocks, hx,
    Matrix.det_fromBlocks_zero₂₁]

theorem main : ∀ (F : Type) [Field F] (r c : ℕ) (p q : GL (Fin (r + c)) F), bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det = (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ∧ bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  intro F _ r c p q hp hq
  obtain ⟨h11, -, h21, h22⟩ := blocks_mul (p : Matrix (Fin (r + c)) (Fin (r + c)) F) (q : Matrix _ _ F)
  refine ⟨?_, ?_, ?_, det_eq_of_bDA_eq_zero _ hp, ?_⟩
  · rw [Units.val_mul, h21, hp, hq]; simp
  · rw [Units.val_mul, h11, hq]; simp
  · rw [Units.val_mul, h22, hp]; simp
  · obtain ⟨k11, -, k21, -⟩ := blocks_mul ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
      (p : Matrix _ _ F)
    have hone : ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) * (p : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hone, hp, Matrix.mul_zero, add_zero] at k11 k21
    have e11 : bAA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
      ext i j; simp [bAA, Matrix.one_apply]
    have e21 : bDA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
      ext i j; simp [bDA, Matrix.one_apply, Fin.ext_iff]; omega
    rw [e11] at k11
    rw [e21] at k21
    have hA : bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
      mul_eq_one_comm.mp k11.symm
    calc bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
        = bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) *
            (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) := by
          rw [hA, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, ← k21, Matrix.zero_mul]

end GlobalTheory.HQStepBlocks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnFaceLevelsBaseLevelSymmetricLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LevelsFace

theorem level_ext'₂ {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {L L' : LevelP Pg r ℂ}
    (h : ∀ g, g ∈ L.H ↔ g ∈ L'.H) (h' : ∀ g hg hg', L.chi ⟨g, hg⟩ = L'.chi ⟨g, hg'⟩) : L = L' := by
  obtain ⟨H, c⟩ := L
  obtain ⟨H', c'⟩ := L'
  obtain rfl : H = H' := Subgroup.ext h
  obtain rfl : c = c' := MonoidHom.ext fun g => h' g.1 g.2 g.2
  rfl

theorem chi_ofLocal_map' {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K] (σ : K →+* ℂ)
    (Hl : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (f : ∀ PP : Pg, Hl PP →* Multiplicative (kP PP.1))
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (g g' : G0 Pg r) (e : g = g') (hg : g ∈ Subgroup.pi Set.univ Hl)
    (hg' : g' ∈ Subgroup.pi Set.univ Hl) :
    Units.map σ.toMonoidHom ((LevelP.ofLocal Hl fun PP => addCharHom (ψ PP.1) (f PP)).chi ⟨g, hg⟩) =
      (LevelP.ofLocal Hl fun PP => addCharHom (σ.toMonoidHom.compAddChar (ψ PP.1)) (f PP)).chi ⟨g', hg'⟩ := by
  subst e
  refine ((congrArg (Units.map σ.toMonoidHom) (MonoidHom.finsetProd_apply _ _ _)).trans (map_prod _ _ _)).trans
    (Eq.trans ?_ (MonoidHom.finsetProd_apply _ _ _).symm)
  exact Finset.prod_congr rfl fun PP _ => Units.ext rfl

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem levels_of_eq (hI : I.Ok) {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    (eG : Gc X.B px ≃* G0 Pg X.toD7.R.r) (hId : IsPlacewiseIdentity X (px := px) eG) :
    ∃ ψ0 : ∀ PP : Pl X.toD7.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ0 ∧
      levPOf eG X.toD7.what₂.embLL (lev0 I) (chr0 I) = P0 Pg X.toD7.R.r ψ0 ∧
      ∃ π : Equiv.Perm (Fin X.toD7.R.r), IsSymOrd X.toD7.R.rS X.toD7.R.k π ∧
        (∀ g, g ∈ (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).H ↔
          reord π g ∈ (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).H) ∧
        ∀ g hg hg', (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).chi ⟨g, hg⟩ =
          (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).chi ⟨reord π g, hg'⟩ := by
  subst hPg
  have hs : ∀ g, eG.symm g = g := fun g =>
    funext fun w => (hId (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  have hle : X.toD7.R.k + X.toD7.R.rS ≤ X.toD7.R.r := by
    have := Formalism.L2.Col.r_eq_sym X.toD7.R
    omega
  refine ⟨fun PP => X.B.embLL.toMonoidHom.compAddChar (psiC I PP), fun PP hP h => ?_, level_ext'₂ (fun g => ?_)
    fun g hg hg' => ?_, (Formalism.L2.Col.symPerm X.toD7.R.r X.toD7.R.k X.toD7.R.rS).symm, fun a => ?_, fun g => ?_, fun g hg hg' => ?_⟩
  · have h1 : psiC I PP = 1 :=
      by
        ext x
        exact X.B.embLL.injective ((DFunLike.congr_fun h x).trans (map_one _).symm)
    rw [psiC_of_mem I hP] at h1
    exact hI.ch_ok.psi_zero_nontrivial_character _ h1
  · show eG.symm g ∈ lev0 I ↔ _
    rw [hs]
    exact Iff.rfl
  · exact chi_ofLocal_map' X.B.embLL _ _ (psiC I) _ _ (hs g) hg hg'
  · rw [Formalism.L2.Col.symPerm_symm_val hle]
    unfold Formalism.L2.Col.symIdxInv
    split_ifs <;> omega
  · show eG.symm g ∈ (Formalism.L2.Col.rPsymF I.Ch).grp ↔ _
    rw [hs]
    show g ∈ Subgroup.pi Set.univ _ ↔ reord _ g ∈ Subgroup.pi Set.univ _
    simp only [Subgroup.mem_pi]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    show g w ∈ Formalism.L2.Col.HPsymF _ _ _ _ ↔ _
    rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap]
    exact Iff.rfl
  · apply Units.ext
    have key : ∀ (w : (X.B.primes px).vGs) (M M' : GL (Fin X.toD7.R.r) (kP w.1)) (e : M' = Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS M)
        (hM : M ∈ Formalism.L2.Col.HPsymF (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS)
        (hM' : M' ∈ unipSym (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k),
        X.B.embLL ((Formalism.L2.Col.chiSymF (I.Ch.psi0 w) X.toD7.R.r X.toD7.R.k X.toD7.R.rS ⟨M, hM⟩ : X.B.LLˣ) : X.B.LL) =
          X.B.embLL (psiC I w.1 (Multiplicative.toAdd (symHom (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k ⟨M', hM'⟩))) := by
      intro w M M' e hM hM'
      subst e
      rw [Formalism.L2.Col.chiSymF_apply, Formalism.L2.Col.chiSym_eq_symHom _ _ _ _ _ hM', psiC_of_mem I w.2]
      rfl
    show X.B.embLL (((Formalism.L2.Col.rPsymF I.Ch).chr ⟨eG.symm g, hg⟩ : X.B.LLˣ) : X.B.LL) = _
    rw [Formalism.L2.Col.LevFam.chr_apply, Units.coe_prod, map_prod]
    erw [MonoidHom.finsetProd_apply, Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact key w _ _ (congrArg (fun h : G0 (X.B.primes px).vGs X.toD7.R.r =>
      Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS (h w)) (hs g)).symm _ _

theorem levelsL_face0 : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  intro X px I hX U Xg tr L eG hI hL hId
  exact levels_of_eq X I hI hL.Pg eG hId

end GlobalTheory.Mem.R3.LevelsFace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DGamDvdOfMinkMult
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions _root_.Formalism.L2.Col

theorem le_N_of_mem_gamRanks (R : Ranks) {n : ℕ} (hn : n ∈ gamRanks R) : n ≤ R.N R.m := by
  have hY : ∀ j, j ≤ R.m → R.rankY j ≤ R.N R.m := by
    intro j hj
    have : j * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ hj
    unfold Ranks.rankY Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have hm := R.two_le_m
  simp only [gamRanks, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj.2) _
  · exact hY _ le_rfl
  · exact hY _ (Nat.sub_le _ _)
  · simpa [Ranks.rankY, Ranks.nV] using hY 1 (by omega)

theorem DGam_dvd_of_minkMult : ∀ {X : Fields} (R : Ranks), X.Ok →
    ∀ M, Formalism.MainNotions.MinkMult (2 * X.f * R.N R.m) M → DGam X.E R ∣ M := by
  intro X R hX M hM
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  refine DGam_dvd (posStar_of_ok hX) R fun a ha => ?_
  obtain ⟨n, hn, N, hN, hUni, rfl⟩ := Set.mem_iUnion₂.1 ha
  haveI := autO_finite (posStar_of_ok hX) (hcnt_isFullLattice_of_unimodular hN hUni)
  refine GlobalTheory.DGamOnRecord.card_dvd_of_minkMult hM ?_ _
  rw [hE]
  exact Nat.mul_le_mul_left _ (le_N_of_mem_gamRanks R hn)

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOneStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ), letI : MeasurableSpace (P.adicCompletion L) := borel _; ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)), ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  first | exact @GlobalTheory.HaarMat.exists_haar_intMat | exact GlobalTheory.HaarMat.exists_haar_intMat | (intros; apply GlobalTheory.HaarMat.exists_haar_intMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomialStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (b e : Ω) (m : ℕ) (f : Polynomial ℤ), IsIntegral ℤ e → σ e = e → A'.valuation (1 - e) < 1 → A'.valuation (m : Ω) = 1 → f.Monic → f.natDegree = m → Polynomial.aeval b f = 0 → ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧ e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  first | exact @GlobalTheory.exists_roots_fixed_of_mem_Ine | exact GlobalTheory.exists_roots_fixed_of_mem_Ine | (intros; apply GlobalTheory.exists_roots_fixed_of_mem_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta ∧ ∃ io, ({ R with ioP := io } : RealDat D A Ks).thP_ioP := by
  first | exact @GlobalTheory.JointHarm.exists_ioP | exact GlobalTheory.JointHarm.exists_ioP | (intros; apply GlobalTheory.JointHarm.exists_ioP <;> assumption)
end

