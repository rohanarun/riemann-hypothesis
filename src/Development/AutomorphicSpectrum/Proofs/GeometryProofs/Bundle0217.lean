module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open _root_.GlobalTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

variable {X Y : Scheme.{0}}

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valF, dite_eq_left h, valAt', dite_eq_left h, valAt]
  · rw [valF, dite_eq_right h, valAt', dite_eq_right h]

theorem top_le_wchart {K : Type} [Fintype K] (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (i : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => i) :=
  fun p hp => Set.mem_iInter.2 fun _ => by
    have := h hp
    simpa using this

theorem valAt'_g_const {K : Type} [Fintype K] [Unique K] (L : LB X) (φ : Y ⟶ X) (e : ℤ) (x : Sp ℂ ⟶ Y) (i i' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))) :
    valAt' x _ ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i')).val =
      valAt' (x ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val ^ e := by
  have hle : LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i') ≤
      φ ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ default)) (inf_le_right.trans (LB.wchart_le L _ _ default))
  have key : ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i') :
      Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) =
      (res hle (pullU φ _ (L.g i i'))) ^ e :=
    Fintype.prod_unique (M := Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) _
  refine (congrArg (fun u : Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓
    LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ => valAt' x _ u.val) key).trans ?_
  refine (valAt'_units_zpow x h _ e).trans ?_
  congr 1
  exact (valAt'_map x _ _ h).trans (valAt'_comp x φ _ _)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem exists_chart_pt (a : ArchFrame P z g) (w : Fin g → ℂ) : ∃ i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := by
  have h : a.pt w (default : PrimeSpectrum ℂ) ∈ (⨆ i, P.L.U i : G.left.Opens) := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 h
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

theorem top_le_frame (a : ArchFrame P z g) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (P.L.pull a.φ).U (fun _ => i) :=
  top_le_wchart (K := PUnit) P.L a.φ (a.u.ex w).left i h

theorem top_le_sec (a : ArchFrame P z g) (n : ℕ) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ a.pt w ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) :=
  top_le_wchart (K := Fin 1) P.L (𝟙 G.left) (a.pt w) i (by simpa using h)

theorem fr_change (a : ArchFrame P z g) (w : Fin g → ℂ) (i j : P.L.ι) (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i)
    (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    a.u.fr (fun _ => i) w = valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val * a.u.fr (fun _ => j) w := by
  have h : ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ ((P.L.pull a.φ).U (fun _ => i) ⊓ (P.L.pull a.φ).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_frame a w i hi, top_le_frame a w j hj⟩
  refine (a.u.fr_compat _ _ w h).trans ?_
  have := valAt'_g_const (K := PUnit) P.L a.φ 1 (a.u.ex w).left i j h
  rw [zpow_one] at this
  exact congrArg (· * a.u.fr (fun _ => j) w) this

theorem sec_change (a : ArchFrame P z g) {n : ℕ} (s : Out.H0 P.L n) (w : Fin g → ℂ) (i j : P.L.ι)
    (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    valF (a.pt w) _ (s.f fun _ => i) =
      valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val ^ n * valF (a.pt w) _ (s.f fun _ => j) := by
  have h : ⊤ ≤ a.pt w ⁻¹ᵁ ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_sec a n w i hi, top_le_sec a n w j hj⟩
  have e := congrArg (valAt' (a.pt w) _) (s.compat (fun _ => i) (fun _ => j))
  rw [valAt'_mul, valAt'_map _ _ _ h, valAt'_map _ _ _ h] at e
  have t := valAt'_g_const (K := Fin 1) P.L (𝟙 G.left) (n : ℤ) (a.pt w) i j h
  rw [Category.comp_id, zpow_natCast] at t
  rw [valF_eq_valAt', valF_eq_valAt', e, t]

theorem unique_fn (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) : ∃! θ, a.IsFn s θ := by
  choose c hc using exists_chart_pt a
  have hne : ∀ w i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → a.u.fr (fun _ => i) w ≠ 0 :=
    fun w i h => a.u.fr_ne _ w (top_le_frame a w i h)
  refine ⟨fun w => valF (a.pt w) _ (s.f fun _ => c w) / a.u.fr (fun _ => c w) w ^ n, ?_, ?_⟩
  · intro i w hi
    have h1 := fr_change a w i (c w) hi (hc w)
    have h2 := sec_change a s w i (c w) hi (hc w)
    have n1 := hne w (c w) (hc w)
    show _ = _ / _ * _
    rw [h2, h1, mul_pow]
    field_simp
  · intro θ hθ
    funext w
    have := hθ (c w) w (hc w)
    rw [this, mul_div_assoc, div_self (pow_ne_zero _ (hne w _ (hc w))), _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

theorem GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n), ∃! θ, a.IsFn s θ :=
  by
  intro S G _ _ P z g a n s
  exact GlobalTheory.CompanionTheory.Ar.Sl.FrameFn.unique_fn a n s
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationDimEqPpDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem rank_eq_unif_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (M : LB A.left) (g : ℕ) (u : HolUnif A M g), IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → D.g = g := by
  intro E _ _ _ H L _ _ D σ A _ φ M g u hp h1 h2
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  obtain ⟨Mσ, -⟩ := GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre (Sp (𝓞 L)) D.t.G L (𝟙 _) D.B.carrier D.MB σ
  have hp' : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) φ := by
    rwa [Category.comp_id]
  obtain ⟨e, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv _ D.t.G _ _ Mσ A φ M g u hp' h1 h2
  have hf : Module.finrank ℂ (Fibre σ D.B.carrier) = g := by
    rw [e.finrank_eq, Module.finrank_fin_fun]
  have hr : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank (𝓞 L) D.B.carrier :=
    GroundTheory.Heights₂.Heights.FibreMahlerForms.finrank_fibreSpace D.B.metric σ
  have hq : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank ℂ (Fibre σ D.B.carrier) :=
    (FibreSpace.equiv D.B.metric σ).symm.finrank_eq
  change Module.finrank (𝓞 L) D.B.carrier = g
  rw [← hr, hq, hf]

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationIsoTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.TanIso

open GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A']

theorem isTangent_comp (f : A' ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A'} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  have h₁ : η[A'] ≫ f = η[A] := IsMonHom.one_hom f
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, h₁]

theorem linLift_injective {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (e : A' ≅ A) [IsMonHom e.hom] (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u'.ex z ≫ e.hom) :
    Function.Injective F := by
  refine (injective_iff_map_eq_zero F).2 fun z hz => ?_
  have hone : ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ e.hom) = 1 := by rw [MonObj.one_comp]
  have hmem : ∀ c : ℂ, c • z ∈ u'.Λ := fun c => by
    refine (u'.ker _).1 ?_
    have h0 : u'.ex (c • z) ≫ e.hom = 1 := by
      rw [← hF, map_smul, hz, smul_zero]
      exact (u.ker 0).2 u.Λ.zero_mem
    have : (u'.ex (c • z) ≫ e.hom) ≫ e.inv = ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ e.hom) ≫ e.inv := by rw [h0, hone]
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using this
  haveI := u'.discrete
  let φ : ℂ → u'.Λ := fun c => ⟨c • z, hmem c⟩
  have hφ : Continuous φ := Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hφ (x := 1) (y := 0)
  simpa [φ] using congrArg Subtype.val h

theorem isDiff_of_comp {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (e : A' ≅ A) [IsMonHom e.hom] (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u'.ex z ≫ e.hom)
    {c : Fin g' → ℂ} {v : epsR ℂ ⟶ A'} (ht : IsTangent v) (hd : u.IsDiff (F c) (v ≫ e.hom)) : u'.IsDiff c v := by
  have a0 := isDerivAt0_of_isDiff u (isTangent_comp e.hom ht) hd
  have a1 := isDerivAt0_comp_linMap (isHolTo_ex u) F a0
  have a2 := GlobalTheory.FibreDeriv.isDerivAt0_comp a1 e.inv.left
  have l₁ : (v ≫ e.hom).left ≫ e.inv.left = v.left := by
    rw [← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [l₁, show (fun z => (u.ex (F z)).left ≫ e.inv.left) = fun z => (u'.ex z).left from funext fun z => by
    rw [← Over.comp_left, hF, Category.assoc, e.hom_inv_id, Category.comp_id]] at a2
  exact fun U h f => a2.2 U h f

theorem tangentCoords_of_iso : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (M : LB A.left) (M' : LB A'.left) (g : ℕ) (u : HolUnif A M g) (u' : HolUnif A' M' g) (e : A' ≅ A) [IsMonHom e.hom], IsAbelianScheme A → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) := by
  intro A A' _ _ M M' g u u' e _ hAb d₁ d₂
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun w => (u'.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u') e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hAb M g g u d₁ d₂
    (fun w => u'.ex w ≫ e.hom) (fun p q => by rw [u'.ex_add, MonObj.mul_comp]) hol
  have hinj : Function.Injective F := linLift_injective u u' e F hF
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hinj
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · obtain ⟨w₀, hw₀, huniq⟩ := d₁ _ (isTangent_comp e.hom hv)
    obtain ⟨c, rfl⟩ := hsurj w₀
    refine ⟨c, isDiff_of_comp u u' e F hF hv hw₀, fun c' hc' => hinj (huniq _ ?_)⟩
    exact GlobalTheory.CompanionTheory.Ar.HodgeUniq.isDiff_comp u u' d₂ e.hom F hF hv hc'
  · obtain ⟨t, ⟨ht, hd⟩, huniq⟩ := d₂ (F w)
    have hcomp : (t ≫ e.inv) ≫ e.hom = t := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    have hv : IsTangent (t ≫ e.inv) := GlobalTheory.CompanionTheory.Ar.HodgeUniq.tangent_of_iso e ht hcomp
    refine ⟨t ≫ e.inv, ⟨hv, isDiff_of_comp u u' e F hF hv (hcomp.symm ▸ hd)⟩, fun v' hv' => ?_⟩
    have h := huniq (v' ≫ e.hom) ⟨isTangent_comp e.hom hv'.1,
      GlobalTheory.CompanionTheory.Ar.HodgeUniq.isDiff_comp u u' d₂ e.hom F hF hv'.1 hv'.2⟩
    rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

end GlobalTheory.CompanionTheory.Ar.Sl.TanIso
end

