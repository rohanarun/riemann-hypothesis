module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0128
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointAltBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_integral_point_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H ⊕ CMType H) (m : ℕ) (s : Fin m → 𝔐.Li), 𝔐.IsLinPtOf z P MV A → (𝔐.dR lab).IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → ∃ sL : Fin m → V, IsValues 𝔐 z P MV s sL ∧ LinearIndependent L sL ∧ Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ lab) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A lab m s hLin hfr
  obtain ⟨hact, hlab, -⟩ := hLin
  have hlat := (_root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun r hr => FrameVal.not_inFibre _ _ r hr)).2.2
  exact FrameVal.values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 hact hlab hlat lab s hfr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjointRelationGeneratorCorr
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {S : Type} [CommRing S] {d : ℕ}

theorem aeval_psIn_zero (m : ℕ) (i : Fin 2) (ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S)
    (h : ∀ l, ψ (i, l) = 0) (f : PS S 1 d) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.aeval ψ (psIn d m ![i] f) = 0 := by
  have e : (ψ ∘ fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin 2) p.1, p.2)) = 0 := by
    funext p
    obtain ⟨k, l⟩ := p
    simpa using h l
  rw [psIn, MvPolynomial.aeval_rename, e, MvPolynomial.aeval_zero, FBIdPh.cc_psTrunc, hf, map_zero]

theorem aeval_psIn_X (m : ℕ) (i : Fin 2) (ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S)
    (h : ∀ l, ψ (i, l) = MvPolynomial.X ((0 : Fin 1), l)) (f : PS S 1 d) :
    MvPolynomial.aeval ψ (psIn d m ![i] f) = psTrunc m f := by
  have e : (ψ ∘ fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin 2) p.1, p.2)) = MvPolynomial.X := by
    funext p
    obtain ⟨k, l⟩ := p
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simpa using h l
  rw [psIn, MvPolynomial.aeval_rename, e, MvPolynomial.aeval_X_left_apply]

abbrev axP (d : ℕ) (S : Type) [CommRing S] (b : Bool) : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S :=
  fun p => (if b then ![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)]
    else ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

theorem constantCoeff₂ (b : Bool) (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (axP d S b p) = 0 := by
  obtain ⟨k, j⟩ := p
  cases b <;> fin_cases k <;> simp [axP]

abbrev fstP (f : Fin d → PS S 1 d) (m : ℕ) : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S :=
  fun p => (![fun j => psIn d m ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2

abbrev sndP (f : Fin d → PS S 1 d) (m : ℕ) : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (f j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2

abbrev actJ (f : Fin d → PS S 1 d) (m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)

theorem fstP_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (fstP f m p) = 0 := by
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simpa [fstP] using (FBIdPh.cc_psIn d m ![0] (f j)).trans (hf j)
  · simp [fstP]

theorem sndP_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (sndP f m p) = 0 := by
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP]
  · simpa [sndP] using (FBIdPh.cc_psIn d m ![1] (f j)).trans (hf j)

theorem trunc_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 1 × Fin d) : MvPolynomial.constantCoeff (psTrunc m (f p.2)) = 0 :=
  (FBIdPh.cc_psTrunc m _).trans (hf _)

theorem ax_fst_true (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m true).comp (jetSubstP m (fstP f m)) = axJ d m true := by
  refine (FBIdPh.jetSubstP_comp m (fstP f m) (axP d S true) (fstP_cc f hf m) (constantCoeff₂ true)).trans ?_
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · exact aeval_psIn_zero m 0 _ (fun _ => rfl) _ (hf j)
  · simp [fstP, axP]

theorem ax_snd_true (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m true).comp (jetSubstP m (sndP f m)) = (actJ f m).comp (axJ d m true) := by
  refine (FBIdPh.jetSubstP_comp m (sndP f m) (axP d S true) (sndP_cc f hf m) (constantCoeff₂ true)).trans ?_
  refine Eq.trans ?_ (FBIdPh.jetSubstP_comp m (axP d S true) _ (constantCoeff₂ true) (trunc_cc f hf m)).symm
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP, axP]
  · refine (aeval_psIn_X m 1 _ (fun _ => rfl) _).trans ?_
    simp [axP]

theorem ax_fst_false (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m false).comp (jetSubstP m (fstP f m)) = (actJ f m).comp (axJ d m false) := by
  refine (FBIdPh.jetSubstP_comp m (fstP f m) (axP d S false) (fstP_cc f hf m) (constantCoeff₂ false)).trans ?_
  refine Eq.trans ?_ (FBIdPh.jetSubstP_comp m (axP d S false) _ (constantCoeff₂ false) (trunc_cc f hf m)).symm
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · refine (aeval_psIn_X m 0 _ (fun _ => rfl) _).trans ?_
    simp [axP]
  · simp [fstP, axP]

theorem ax_snd_false (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m false).comp (jetSubstP m (sndP f m)) = axJ d m false := by
  refine (FBIdPh.jetSubstP_comp m (sndP f m) (axP d S false) (sndP_cc f hf m) (constantCoeff₂ false)).trans ?_
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP, axP]
  · exact aeval_psIn_zero m 1 _ (fun _ => rfl) _ (hf j)

theorem ax_copy_zero (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) ≠ b) :
    (axJ (S := S) d m b).comp (jetCopy d m i) =
      (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  have h0 : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X (k, j))) = 0 := by
    simp [jetAug, liftJet]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h0, map_zero, jetCopy, jetMap_mk, MvPolynomial.aeval_X, axJ_X]
  simp [axV, hi]

theorem ax_copy_id (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) = b) :
    (axJ (S := S) d m b).comp (jetCopy d m i) = AlgHom.id S _ := by
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, axJ_X, AlgHom.id_apply]
  simp [axV, hi]

end Alg

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem pt_killed (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) (b : Bool)
    (i : Fin 2) (hi : (i = 1) ≠ b) : homAt x0 (axJ (S := S) d m b) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, ax_copy_zero m b i hi, ← homAt_comp, Category.assoc, hz m]
  exact MonObj.comp_one _

theorem pt_kept (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) = b) :
    homAt x0 (axJ (S := S) d m b) ≫ jptG t x0 d x m i = x m := by
  rw [jptG, ← Category.assoc, homAt_comp, ax_copy_id m b i hi, homAt_id, Category.id_comp]

theorem val_axis (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (hax : FrAxes t x0 d x e) (a : 𝓞 E) (wL : FrGauge.AdTy t a)
    (hrel : FrGauge.AdRel t x0 d x act ad e a wL) (m : ℕ) (b : Bool)
    (hb : ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) (ad a) = 1)
    (r₁ r₂ : (jOG x0 d m 1).left ⟶ (jOG x0 d m 1).left)
    (h₁ : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (jetSubstP m (fstP (act a) m))).left =
      r₁ ≫ (homAt x0 (axJ (S := S) d m b)).left)
    (h₂ : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (jetSubstP m (sndP (act (H.bar a)) m))).left =
      r₂ ≫ (homAt x0 (axJ (S := S) d m b)).left)
    (y : (jOG x0 d m 1).left) (J : ((jOG x0 d m 1).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val wL ((homAt x0 (axJ (S := S) d m b)).left ≫
      (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) y J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel m
  have hA : LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (axJ (S := S) d m b)).left) (LB.oneGen t.PP.L) := by
    cases b
    · exact (hax m).2
    · exact (hax m).1
  have hv : ∀ r : (jOG x0 d m 1).left ⟶ (jOG x0 d m 1).left,
      val (e m) (r ≫ (homAt x0 (axJ (S := S) d m b)).left) y J = 1 := fun r =>
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hA r).trans (val_one _))
  have E := val_corr hJ hc (homAt x0 (axJ (S := S) d m b)).left
  rw [val_mul hJ, val_pull hJ, GermB.val_scale t _ _ _ _ _ y J hJ] at E
  have p₁ : val (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (homAt x0 (axJ (S := S) d m b)).left y J = 1 :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (e m) r y J) h₁).trans (hv r₁))
  have p₂ : val (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
      (homAt x0 (axJ (S := S) d m b)).left y J = 1 :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (e m) r y J) h₂).trans (hv r₂))
  have hU : Units.map ((axJ (S := S) d m b : _ →ₐ[S] _) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 1 × Fin d) m) u = 1 :=
    Units.ext (by
      rw [Units.coe_map, hu]
      exact (psJet_ev_ax d m (ad a) b).symm.trans ((congrArg (psJet m) hb).trans (psJet_one m)))
  have p₃ : gm (homAt x0 (axJ (S := S) d m b)).left y ⊤ (unitΓ u) = 1 := by
    rw [FrRatio.gm_map, hU, unitΓ_one, map_one]
  rw [p₁, p₂, p₃, _root_.mul_one, _root_.mul_one] at E
  exact E

theorem lift_true (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) :
    (homAt x0 (axJ (S := S) d m true)).left ≫
        (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left =
      (lift (1 : jOG x0 d m 1 ⟶ t.G) (x m)).left := by
  rw [← Over.comp_left, comp_lift, pt_killed t x0 d x hz m true 0 (by simp),
    pt_kept t x0 d x m true 1 (by simp)]

theorem lift_false (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) :
    (homAt x0 (axJ (S := S) d m false)).left ≫
        (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left =
      (lift (x m) (1 : jOG x0 d m 1 ⟶ t.G)).left := by
  rw [← Over.comp_left, comp_lift, pt_kept t x0 d x m false 0 (by simp),
    pt_killed t x0 d x hz m false 1 (by simp)]

end Frame

theorem adAxes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (d : ℕ)
    (g : GermAt t x d) (a : 𝓞 E) (wL : FrGauge.AdTy t a), wL.IsGen →
    FrGauge.AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → ∀ m,
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (1 : jOG x d m 1 ⟶ t.G) (g.x m)).left)
      (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (g.x m) (1 : jOG x d m 1 ⟶ t.G)).left)
      (LB.oneGen t.PP.L) := by
  intro E _ _ _ H _ _ X t S _ x d g a wL _ hrel m
  have hL := t.PP.isLB
  have hc : ∀ c j, MvPowerSeries.constantCoeff (g.B.A.act c j) = 0 := g.B.A.const
  refine ⟨corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_pull hJ, val_one, Category.id_comp, ← lift_true t x d g.x g.chart.zero m]
    refine val_axis t x d g.x g.B.A.act g.B.ad g.e g.axes a wL hrel m true (g.B.adjoint_zero_fst a) (𝟙 _)
      (homAt x (actJ (g.B.A.act (H.bar a)) m)).left ?_ ?_ y J hJ
    · rw [← Over.comp_left, homAt_comp, ax_fst_true _ (hc a) m, Category.id_comp]
    · rw [← Over.comp_left, homAt_comp, ax_snd_true _ (hc _) m, ← homAt_comp, Over.comp_left]
  · rw [val_pull hJ, val_one, Category.id_comp, ← lift_false t x d g.x g.chart.zero m]
    refine val_axis t x d g.x g.B.A.act g.B.ad g.e g.axes a wL hrel m false (g.B.adjoint_zero_snd a)
      (homAt x (actJ (g.B.A.act a) m)).left (𝟙 _) ?_ ?_ y J hJ
    · rw [← Over.comp_left, homAt_comp, ax_fst_false _ (hc _) m, ← homAt_comp, Over.comp_left]
    · rw [← Over.comp_left, homAt_comp, ax_snd_false _ (hc _) m, Category.id_comp]

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar

theorem lieModel_liftBaseChange : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ X) (V : Type) [AddCommGroup V] [Module R V] (M : LieModel G x V), ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T) (M' : LieModel G (spMap (algebraMap R R') ≫ x) T) (j : V →ₗ[R] T), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  intro X G _ _ _ R R' _ _ _ x V _ _ M
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists X G R' (spMap (algebraMap R R') ≫ x)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  haveI tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = spMap (algebraMap R R') ≫ x := rfl
  have spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) :
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (g.comp f)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have spec_dual_alg :
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have spec_fst_dual :
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']
  have spec_dual_eps (c : R) :
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (epsMul c)) =
      Spec.map (CommRingCat.ofHom (epsMul ((algebraMap R R') c))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl']
  let b : epsAt (spMap (algebraMap R R') ≫ x) ⟶ epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R')))) (by
      change _ ≫ _ ≫ x = _ ≫ (spMap (algebraMap R R') ≫ x)
      rw [← Category.assoc, spec_dual_alg, Category.assoc])
  have hb : ∀ {v : epsAt x ⟶ G}, IsTanAt G x v →
      IsTanAt G (spMap (algebraMap R R') ≫ x) (b ≫ v) := by
    intro v hv
    change _ ≫ Spec.map _ ≫ v.left = _
    rw [← Category.assoc, spec_fst_dual, Category.assoc, hv]
    exact congrArg (·.left)
      (comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) hφ :
        Over.mk (spMap (algebraMap R R') ≫ x) ⟶ Over.mk x))
  have hs (c : R) : b ≫ LieTangent.epsScale x c =
      LieTangent.epsScale (spMap (algebraMap R R') ≫ x) (algebraMap R R' c) ≫ b :=
    Over.OverMorphism.ext (spec_dual_eps c)
  have ex : ∀ e, ∃ t, M'.pt t = b ≫ M.pt e :=
    fun e => M'.onto _ (hb (M.tan e))
  choose f hf using ex
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M'.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          hs, Category.assoc]) }
  have hl : ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  exact ⟨T, iT, mT, mR, tower, M', j, hl, _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange X G R R' x V T M M' j hl⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProjectiveCoordModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem mem_of_isIntegral_of_isLocAt {Ω : Type} [Field Ω] [CharZero Ω] (R : Subring Ω) [IsFractionRing R Ω]
    (A : Subalgebra ℚ Ω) (hs : Algebra.Smooth ℚ A) (q : Ideal A) (hq : q.IsPrime) (h : IsLocAt A q R)
    (a : Ω) (ha : IsIntegral R a) : a ∈ R := by
  have hAR : ∀ b : A, (b : Ω) ∈ R := fun b =>
    (h b).2 ⟨1, fun h1 => hq.ne_top ((Ideal.eq_top_iff_one q).2 h1), by simp⟩
  letI : Algebra A R := (RingHom.codRestrict A.val.toRingHom R hAR).toAlgebra
  have hmap : ∀ b : A, ((algebraMap A R b : R) : Ω) = b := fun _ => rfl
  have hne : ∀ s : A, s ∉ q → (s : Ω) ≠ 0 := fun s hs0 h0 =>
    hs0 (by rw [show s = 0 from Subtype.ext h0]; exact q.zero_mem)
  haveI : IsLocalization.AtPrime R q :=
    { map_units := by
        rintro ⟨s, hs0⟩
        have hs1 : s ∉ q := hs0
        refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, (h _).2 ⟨s, hs1, ?_⟩⟩ : R) (Subtype.ext ?_)
        · rw [mul_inv_cancel₀ (hne s hs1)]; exact A.one_mem
        · simp [hmap, mul_inv_cancel₀ (hne s hs1)]
      surj := by
        rintro ⟨r, hr⟩
        obtain ⟨s, hs1, hsr⟩ := (h r).1 hr
        exact ⟨⟨⟨_, hsr⟩, ⟨s, hs1⟩⟩, Subtype.ext (by simp [hmap, mul_comm])⟩
      exists_of_eq := by
        intro x y hxy
        exact ⟨1, by
          have : (x : Ω) = y := by simpa [hmap] using congrArg (Subtype.val) hxy
          rw [Subtype.ext this]⟩ }
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  obtain ⟨r, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := Ω)).1 ha
  exact r.2

end GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ X ξ N x e Ab hall htie hsnc
  let M0 : PModel ℤ x :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }
  obtain ⟨κ', _, y, M', f, hdom, hnorm, -, hat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation ℤ Ω (Fin (N + 1)) x M0 Ω
  have hdom' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ f (RingHom.id Ω) := hdom
  have hiso : ∀ q ∈ genFib ξ, IsoAt M'.ξ f (RingHom.id Ω) q := by
    intro q hq
    have hc : Char0 ξ q := fun r hr hf => hf (hq r hr.pos)
    obtain ⟨A, z, n, P, hp, hP, hloc⟩ := hsnc q hc
    haveI := (_root_.GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring X Ω ξ htie.gen q).1
    exact _root_.GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed X Ω ξ M'.X M'.ξ f q (hat q)
      (fun a ha => mem_of_isIntegral_of_isLocAt _ A hp.smooth P hP hloc a ha)
  obtain ⟨N', x', hx'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite M'.X Ω M'.ξ ℤ κ' y M'.tie
  have hone := GlobalTheory.T.coords_single_block_segre M'.X Ω M'.ξ N' x' hx'
  have hsnc' := _root_.GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt Ω (Fin (N + 1)) _ x _ X M'.X ξ M'.ξ f e Ab hall M'.all htie hone hdom' hiso hsnc
  exact ⟨Unit, inferInstance, fun _ => Fin (N' + 1), fun _ => inferInstance, fun p => x' p.2,
    { X := M'.X, ξ := M'.ξ, s := M'.s, hover := M'.hover, all := M'.all, tie := hone }, f,
    inferInstance, hdom', hnorm, hsnc'⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagUnderEquivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_under_equiv : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport | exact GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  exact @GlobalTheory.CompanionTheory.Ar.FlagRead.generic_read
end

