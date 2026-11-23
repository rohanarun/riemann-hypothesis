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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsArchimedeanFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.RigScale

open _root_.GlobalTheory GlobalTheory.ArchMetricCompare

theorem eSec_comp_of_cart {S : Scheme.{0}} {G : Over S} [GrpObj G] {z : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) : eSec A ≫ φ = z ≫ eSec G := by
  have e := congrArg (fun q => q.left) (map_one (pushHom h (𝟙_ (Over (Sp ℂ)))))
  have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def scale (u : HolUnif A L g) (c : ℂ) (hc : c ≠ 0) : HolUnif A L g :=
  { u with
    fr := fun j w => c * u.fr j w
    fr_hol := fun i => (u.fr_hol i).const_mul c
    fr_ne := fun i z h => mul_ne_zero hc (u.fr_ne i z h)
    fr_compat := fun i j z h => by
      rw [u.fr_compat i j z h]
      ring }

theorem scale_isAH {u : HolUnif A L g} {c : ℂ} (hc : c ≠ 0) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : (scale u c hc).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l i z hz => ?_⟩
  show c * u.fr i z = _ * (c * u.fr i (z + (l : Fin g → ℂ)))
  rw [h.2.2.2 l i z hz]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.RigScale

namespace GlobalTheory.CompanionTheory.Ar.Sl

open _root_.GlobalTheory GlobalTheory.ArchMetricCompare RigScale

theorem exists_archFrame_of_isAH : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (P.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A G z φ → u.IsAH Hm χ → Nonempty (ArchFrame P z g) := by
  intro S G _ _ P z A _ φ g u Hm χ cart ah
  have he : (u.ex 0).left ≫ φ = z ≫ eSec G := by
    have := eSec_comp_of_cart cart
    rw [show (u.ex 0).left = eSec A from GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u]
    exact this
  obtain ⟨i₀, h₀⟩ : ∃ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i :=
    (exists_chart P.isLB (((u.ex 0).left ≫ φ) (default : PrimeSpectrum ℂ))).imp
      fun _ h => (top_le_preimage_iff_mem _ _).2 h

  have hfr : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => i) :=
    fun i h => (le_pull_iff P.L φ _ _).2 h
  have hz : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      ⊤ ≤ z ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i) := fun i h =>
    (le_pull_iff P.L (eSec G) z _).2 (he ▸ h)
  have hrel : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val =
        valAt' ((u.ex 0).left ≫ φ) (P.L.U i ⊓ P.L.U i₀) (P.L.g i i₀).val *
          valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val := by
    intro i hi
    have hm : ⊤ ≤ z ⁻¹ᵁ ((P.L.pull (eSec G)).U (fun _ => i) ⊓ (P.L.pull (eSec G)).U (fun _ => i₀)) :=
      (top_le_preimage_inf _ _ _).2 ⟨hz i hi, hz i₀ h₀⟩
    have e := congrArg (fun a => valAt' z _ (Units.val a)) (P.rigGen (fun _ => i) (fun _ => i₀))
    have e2 := (valAt'_res z inf_le_left _ hm).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans
      (congrArg₂ (· * ·) rfl (valAt'_res z inf_le_right _ hm))))
    rw [he]
    rw [← val_pull_g P.L (eSec G) z (fun _ => i) (fun _ => i₀) hm]
    exact e2
  have hn : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val ≠ 0 :=
    valAt'_unit_ne_zero z (hz i₀ h₀) _
  have hd := u.fr_ne (fun _ => i₀) 0 (hfr i₀ h₀)
  have hc : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val / u.fr (fun _ => i₀) 0 ≠ 0 :=
    div_ne_zero hn hd
  refine ⟨{ A := A, φ := φ, cart := cart, u := scale u _ hc, Hm := Hm, χ := χ, ah := scale_isAH hc ah, rig := ?_ }⟩
  intro i hi
  have hi' : ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i := hi
  show _ / u.fr (fun _ => i₀) 0 * u.fr (fun _ => i) 0 = _
  have hm : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((P.L.pull φ).U (fun _ => i) ⊓ (P.L.pull φ).U (fun _ => i₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hfr i hi', hfr i₀ h₀⟩
  rw [u.fr_compat (fun _ => i) (fun _ => i₀) 0 hm, val_pull_g P.L φ _ (fun _ => i) (fun _ => i₀) hm, hrel i hi']
  field_simp

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactor
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Fac

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

private theorem eq_of_sp_complex_pts (y y' : ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) : y = y' := by
  have e : ∀ p : PrimeSpectrum ℂ, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime p.asIdeal
  exact PrimeSpectrum.ext (R := ℂ) ((e y).trans (e y').symm)

theorem fn_factor (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ)
    (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) (hθ : a.IsFn s θ)
    (l : a.u.Λ) (w : Fin g → ℂ) :
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  obtain ⟨-, -, -, hfr⟩ := a.ah
  obtain ⟨x0⟩ : Nonempty ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) :=
    ⟨(IsLocalRing.closedPoint ℂ : PrimeSpectrum ℂ)⟩
  obtain ⟨i, hi⟩ : ∃ i : P.L.ι, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt w).base).obj (P.L.U i) := by
    have hx : (a.pt w).base x0 ∈ (⨆ j, P.L.U j) := by
      rw [P.isLB.cover]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun y _ => ?_⟩
    rw [eq_of_sp_complex_pts y x0]
    exact hj
  have hz : ∀ v : Fin g → ℂ, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt v).base).obj (P.L.U i) →
      ⊤ ≤ (TopologicalSpace.Opens.map (CategoryTheory.Over.Hom.left (a.u.ex v)).base).obj
        ((P.L.pull a.φ).U fun _ => i) := by
    intro v hv y hy
    exact Set.mem_iInter.2 fun _ => hv hy
  have hpt : a.pt (w + (l : Fin g → ℂ)) = a.pt w := by
    have h1 : a.u.ex (l : Fin g → ℂ) = 1 := (a.u.ker _).2 l.2
    change CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex (w + (l : Fin g → ℂ)))) a.φ =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex w)) a.φ
    rw [a.u.ex_add, h1, _root_.mul_one]
  have hi' : ⊤ ≤ (TopologicalSpace.Opens.map (a.pt (w + (l : Fin g → ℂ))).base).obj (P.L.U i) := by
    rw [hpt]
    exact hi
  have hA := hθ i w hi
  have hB := hθ i (w + (l : Fin g → ℂ)) hi'
  rw [hpt] at hB
  have hE := hB.symm.trans hA
  have hF := a.u.fr_ne (fun _ => i) (w + (l : Fin g → ℂ)) (hz _ hi')
  have hw : a.u.fr (fun _ => i) w =
      (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) *
        a.u.fr (fun _ => i) (w + (l : Fin g → ℂ)) := hfr l (fun _ => i) w (hz w hi)
  rw [hw, mul_pow] at hE
  apply mul_right_cancel₀ (pow_ne_zero n hF)
  rw [hE]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.Fac
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoordinatesUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameVec

open GlobalTheory.CompanionTheory.Ar.LieSigma

theorem one_left_over {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem isVec_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  intro E _ _ _ H L _ _ D σ a h1 h2 x
  have hw : (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) ≫ D.t.G.hom
      = (epsAt (emb σ)).hom := by
    rw [Category.assoc, Over.w]
    simp only [epsAt, Over.mk_hom, Category.comp_id, emb]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext t <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v : epsAt (emb σ) ⟶ D.t.G := Over.homMk _ hw
  have hvl : v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left := rfl
  have hlift : (v.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := by
    show v.left ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact hvl
  have hsq : v.left ≫ D.t.G.hom = (epsR ℂ).hom ≫ emb σ := hw
  let v' : epsR ℂ ⟶ a.A := Over.homMk (a.cart.1.lift v.left (epsR ℂ).hom hsq) (a.cart.1.lift_snd _ _ _)
  have hφ : v'.left ≫ a.φ = v.left := a.cart.1.lift_fst _ _ _
  have ht : IsTangent v' := by
    unfold IsTangent
    apply a.cart.1.hom_ext
    · have h3 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ (1 : Over.mk (𝟙 (Sp (𝓞 L))) ⟶ D.t.G).left := by
        rw [hvl, ← Category.assoc]
        have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) =
            spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ spMap (TrivSqZeroExt.fstHom (𝓞 L) (𝓞 L) (𝓞 L)).toRingHom := by
          simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 1
          ext t <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
        rw [key, Category.assoc]
        exact congrArg (fun f => spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ f) (D.MB.tan x)
      rw [Category.assoc, hφ, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left a.cart, h3, one_left_over]
      simp
    · have e : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (epsR ℂ).hom = 𝟙 _ := by
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
          ext t <;> simp
        rw [this]
        exact Spec.map_id _
      rw [Category.assoc, Over.w v', e]
      simpa using (Over.w η[a.A]).symm
  obtain ⟨c, hc, hu⟩ := h1 v' ht
  refine ⟨c, ⟨v, hlift, v', hφ, hc⟩, ?_⟩
  rintro c' ⟨v₁, hl₁, v₁', hφ₁, hc₁⟩
  have e₁ : v₁.left = v.left := by
    have : v₁.left ≫ 𝟙 _ = _ := hl₁
    rw [Category.comp_id] at this
    exact this
  have e₂ : v₁' = v' := by
    apply Over.OverMorphism.ext
    apply a.cart.1.hom_ext
    · rw [hφ₁, hφ, e₁]
    · rw [Over.w v₁', Over.w v']
  exact hu c' (e₂ ▸ hc₁)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameVec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_hodgeInnerProduct_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel t.G z V), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → ∃ h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ v w c, HodgeIP t.G t.PP.L z (M.pt v) (M.pt w) c ↔ c = h v w) ∧ (∀ v w, h w v = starRingEnd ℂ (h v w)) ∧ ∀ v, v ≠ 0 → 0 < (h v v).re := by
  intro E _ _ _ H X t z V _ _ M ⟨t', m, hP, hA⟩
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif t'.G t'.PP.L g hab hA hg
  obtain ⟨u, Hm, χ, hex, hH, hχ, hlaw⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical t'.G t'.PP t'.cub g u₀
  obtain ⟨N, J, Θ, hN, hd, hq, hne, hsep⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family t'.G t'.PP.L g u Hm χ t'.PP.isLB hab hA hlaw
  have hpos := _root_.GlobalTheory.CompanionTheory.Ar.HodgeFormAna.pos_of_theta_power g u.Λ u.discrete u.full Hm χ N J Θ hH hχ hN hd hq hne hsep
  have hAH : u.IsAH Hm χ := ⟨hH, hpos, hχ, hlaw⟩
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ t'.PP.L g u
    (by simpa only [hex] using hc)
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL := t'.PP.isLB
  have hM := LB.isLB_pull t.PP.isLB m.φ
  let u₁ : HolUnif t'.G (t.PP.L.pull m.φ) g := GlobalTheory.ArchMetricCompare.carry u hL hM hw₀
  have hAH₁ : u₁.IsAH Hm χ := GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hAH
  have ht₁' : ∀ v, IsTangent v → ∃! w, u₁.IsDiff w v := ht₁
  have ht₂' : ∀ w, ∃! v, IsTangent v ∧ u₁.IsDiff w v := ht₂
  have hcart : IsGrpPullback t'.G t.G z m.φ := m.cart
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv X t.G z V M t'.G m.φ _ g u₁ hcart ht₁' ht₂'
  choose x hxt hxφ hxd using hD
  let h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w => (Real.pi : ℂ) * hermForm Hm (D w) (D v))
    (fun v v' w => by simp [hermForm, Matrix.mulVec_add, dotProduct_add, mul_add])
    (fun c v w => by
      simp [hermForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; ring)
    (fun v w w' => by simp [hermForm, add_dotProduct, mul_add])
    (fun c v w => by simp [hermForm, smul_dotProduct, smul_eq_mul]; ring)
  have hh : ∀ v w, h v w = (Real.pi : ℂ) * hermForm Hm (D w) (D v) := fun _ _ => rfl
  refine ⟨h, fun v w c => ⟨?_, ?_⟩, fun v w => ?_, fun v hv => ?_⟩
  · rintro ⟨-, -, -, A, _, φ, g', u', Hm', χ', v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    have := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks X t.G t.PP.L z t'.G A m.φ φ g g' u₁ u' Hm Hm' χ χ' t.PP.isLB hab hcart h1 ht₁' ht₂' hAH₁ h2
      (x w) (x v) w' v' (D w) (D v) b a (hxt w) (hxt v) (h4.trans (hxφ w).symm) (h3.trans (hxφ v).symm)
      (hxd w) (hxd v) h6 h5
    rw [hh, ← this]
    rfl
  · rintro rfl
    exact ⟨t.PP.isLB, M.tan v, M.tan w, t'.G, inferInstance, m.φ, g, u₁, Hm, χ, x v, x w, D v, D w, hcart, hAH₁,
      hxφ v, hxφ w, hxd v, hxd w, rfl⟩
  · rw [hh, hh, map_mul, Complex.conj_ofReal, GlobalTheory.CompanionTheory.Ar.conj_hermForm hH]
  · rw [hh, Complex.re_ofReal_mul]
    exact mul_pos Real.pi_pos (hpos _ (fun h0 => hv (D.map_eq_zero_iff.1 h0)))

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVector
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameZero

theorem tmul_one_injective {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Projective (𝓞 L) M] (x : M)
    (h : (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x = 0) : x = 0 := by
  have hinj : Function.Injective (Algebra.linearMap (𝓞 L) (ComplexAt σ)) := by
    intro a b hab
    have h1 : σ (a : L) = σ (b : L) := hab
    exact RingOfIntegers.coe_injective (σ.injective h1)
  have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hinj
  have h2 : (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M ((1 : 𝓞 L) ⊗ₜ[𝓞 L] x) =
      (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M 0 := by
    rw [LinearMap.rTensor_tmul, map_zero, Algebra.linearMap_apply, map_one, h]
  have h3 := hr h2
  have h4 := congrArg (TensorProduct.lid (𝓞 L) M) h3
  simpa using h4

theorem core_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (C : InnerProductSpace.Core ℂ V)
    (v : V) (h : (C.inner v v : ℂ).re = 0) : v = 0 := by
  apply C.definite
  have him : (C.inner v v : ℂ).im = 0 := by
    have h1 := C.conj_inner_symm v v
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    linarith
  exact Complex.ext h him

theorem coord_ne_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type)
    [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier)
    (c : Fin D.g → ℂ) (hlen : D.len σ x ^ 2 = Real.pi * (a.herm c c).re) (hx : x ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hx
  have hherm : a.herm 0 0 = 0 := by simp [ArchFrame.herm]
  rw [hherm, Complex.zero_re, mul_zero] at hlen
  have hl : D.len σ x = 0 := by simpa using hlen
  have hnn : 0 ≤ (((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ)).re :=
    (D.B.metric.form σ).re_inner_nonneg _
  have hle := Real.sqrt_eq_zero'.mp hl
  exact tmul_one_injective σ D.B.carrier x (core_eq_zero _ _ (le_antisymm hle hnn))

end GlobalTheory.CompanionTheory.Ar.Sl.FrameZero
end
end

