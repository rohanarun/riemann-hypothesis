module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecordAtOfIsArcFr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjBaseChange
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem exists_cmObj_baseChange : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (K₂ : Type) [Field K₂] [NumberField K₂] (i : K →+* K₂) (σ₂ : K₂ →+* ℂ), σ₂.comp i = σ₁ → ∃ (ρ₂ : 𝓞 K₂) (X₂ : GlobalTheory.CM.CMObj H K₂ ρ₂ σ₂ p q) (_ : SABMap X₂.B.t X.B.t (spMap (RingOfIntegers.mapRingHom i))), (ρ₂ : K₂) = i (ρ : K) ∧ X₂.hh = X.hh := by
  intro _ E _ _ _ H K _ _ ρ σ₁ p q X K₂ _ _ i σ₂ h
  have extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ}
      (X : GlobalTheory.CM.CMObj H K ρ σ p q) (j : K →+* K₂) (σ' : K₂ →+* ℂ)
      (h : σ'.comp j = σ) :
      ∃ (X' : GlobalTheory.CM.CMObj H K₂ (RingOfIntegers.mapRingHom j ρ) σ' p q)
        (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
        (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
        X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := open GlobalTheory.CM GlobalTheory.CMExistsCompare in by
    set f := RingOfIntegers.mapRingHom j with hf
    have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
    choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
    obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
    have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
    choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
    have hpt := spMap_int j h
    refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K₂ j X.split |>.1
              ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
              A := A', B := B'
              typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
              typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
              typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
              hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
    · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
      have e := congrArg Over.Hom.left ((X.lin i).2 c)
      simp only [Over.comp_left] at e
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
        (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
    · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
      choose pA hA using fun b => exists_ptEquiv (a b) hpt
      obtain ⟨x, hx⟩ := X.onto (pB y)
      refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
      rw [hx, map_list_prod, List.map_ofFn]
      congr 2
      funext i
      apply Over.OverMorphism.ext
      simp only [Function.comp_apply]
      rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
      erw [hφ]
      rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
    · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
        (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
        ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
      rw [hpt]
      exact X.weil i
  obtain ⟨X₂, -, mb, hh, -⟩ := extend X i σ₂ h
  exact ⟨_, X₂, mb, rfl, hh⟩

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FinLocalAtOfIntModel
section
noncomputable section

namespace GlobalTheory.FinLocalTan

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  have c' := congrArg (fun z => cubV D.cub y J ((origin R) ≫ DegPre.cT D (epsR R) χ)
    ((origin R) ≫ ν.b) z) h₁'
  have cz (x x' : Over.mk (𝟙 (Sp R)) ⟶ D.P.A) : cubV D.cub y J x x' 1 = 1 := by
    have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
      simp [faceMap, x2, pzero, Hom.one_def]
    refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
    refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
    show val D.cub.t (lift x (lift x' 1)).left y J = _
    rw [hm, Over.comp_left]
    all_goals rfl
  have c := c.trans (c'.trans (cz _ _))
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

theorem gtTanR_of_letBC {K K' : Type} [Field K] [Field K'] {f : K →+* K'} {D : DegPre K} {D' : DegPre K'}
    {p : IsPullDeg f D D'} {ν : GtPt D (epsR K)} {ν' : GtPt D' (epsR K')} (h : LetBC p ν ν') (ht : GtTanR ν') :
    GtTanR ν := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν').1 ht
  have h : ν'.b.left ≫ prj p = spMap (Formalism.L2.Pj.dualMap f) ≫ ν.b.left ∧ ∀ χ,
      (∀ i, DegPre.gtφT D' (epsR K') ν'.b χ i ≫ prj p = spMap (Formalism.L2.Pj.dualMap f) ≫ DegPre.gtφT D (epsR K) ν.b (p.xe χ) i) ∧
      PMaps p.w _ _ DegPre.gtε (ν'.s χ) (ν.s (p.xe χ)) (spMap (Formalism.L2.Pj.dualMap f)) := ⟨h.1, fun χ => ⟨(h.2 χ).1, (maps_iff p.w _ _ _ (ν'.s χ) (ν.s (p.xe χ)) _ _
    (GeneratorPullback.pullAlong_le _ _ _ _ _ (h.2 χ).1) (fun _ => rfl)).1 (h.2 χ).2⟩⟩
  have sq : (origin K').left ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap f ≫ (origin K).left := by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
    exact RingHom.ext fun x => by simp [Formalism.L2.Pj.dualMap]
  have : Flat (spMap f) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap f) := by
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact ⟨fun y => ⟨(default : PrimeSpectrum K'), Subsingleton.elim _ _⟩⟩
  have : Epi (spMap f) := Flat.epi_of_flat_of_surjective _
  have hb : origin K ≫ ν.b = 1 := by
    refine Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)
    have o : (origin K').left ≫ ν'.b.left = eSec D'.P.A := (congrArg (fun q => q.left) h₁).trans (Category.id_comp _)
    have o' : (1 : Over.mk (𝟙 (Sp K)) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
    rw [o', Over.comp_left]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sq.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h.1.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) o).trans p.he)))))
  refine (gtTanR_iff ν).2 ⟨hb, fun χ y J hJ => ?_⟩
  obtain ⟨x, rfl⟩ := p.xe.surjective χ
  have C := corr_of_val_flat_surjective (spMap f) D.P.isLB
    (t := LB.pullGen D.P.L _ _ (ν.s (p.xe x)) (origin K).left) (t' := LB.oneGen D.P.L) fun z I hI => by
      obtain ⟨I', hI'⟩ := DegPull.exists_good' D'.P.isLB z
      have e := (ConstFam.pmaps_val (h.2 x).1 (h.2 x).2 (origin K').left hI hI').trans (congrArg (· * _)
        (FormalPoint.prod_gtφT (origin K') ν'.b x (ConstFam.wVal p.w z I I')))
      rw [h₁, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul, sq] at e
      exact (val_pull hI _ _ _).trans (e.trans ((h₂ x z I' hI').trans (val_one _).symm))
  have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ C (𝟙 _)).trans (val_one _))
  rwa [Category.id_comp] at v

end GlobalTheory.FinLocalTan

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem finLocal_vV_nonneg {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] {v : V} (hv : algebraMap V K v ≠ 0) : 0 ≤ vV V (algebraMap V K v) := by
  have h1 : valV V (algebraMap V K v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have h2 := (WithZero.log_le_log (valV_ne_zero (V := V) hv) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  simp only [vV]
  omega

theorem finLocal_vV_pos {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] {v : V} (hv : Irreducible v) : 0 < vV V (algebraMap V K v) := by
  have h0 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hv.ne_zero
  have h1 : valV V (algebraMap V K v) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 ((IsLocalRing.mem_maximalIdeal v).2 hv.not_isUnit)
  have h2 := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  simp only [vV]
  omega

theorem finLocalAt_of_intModel :
    Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (M : IntModel d Tv io Wl) (la : HeightOneSpectrum (𝓞 c.F)) (eL : ℕ) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tv.Fr) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Tv.Fr) (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), d.OverBase → Tv.FinRes → OverLa w Tv.V io 1 → OverLa la Tv.V (io.comp (algebraMap c.F K₁)) eL → Yw.N4 → PushInvertible Yw.t.G Yw.t.PP.L → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → (M.γ ≠ 0 ∧ vV Tv.V M.γ = vth) → (∀ τ k, lam τ k ≠ 0 ∧ vV Tv.V (lam τ k) = vη τ k) → (∀ τ, (A τ).det ≠ 0) → (∀ τ k l, M.g τ k l = lam τ k * A τ k l) → (∀ τ k l, A τ k l = 0 ∨ -(m : ℤ) ≤ vV Tv.V (A τ k l)) → ∀ a n, FinLocalAt d w n vth vη m (intAt Xo c a n la) := by
  intro h1 h2 hU h5 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w Tv io Wl Yw M la eL lam A vth vη m hob hfin how hola h4
    hpush hbas hγ hlam hdet hg hA a n
  obtain ⟨Z, ιT, hc, hn, hs⟩ := (exists_finSite_norm_eq_zpow_siteAlg K₁ w).2 Tv io hfin how
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) Tv.V := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  obtain ⟨χ, hχ, -⟩ := h4 Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hbase, -, hgen, t, mm, P, φ, he, ww, e, hspec⟩ := (hχ χ).1 rfl
  let W : Wit Yw M.aw χ := ⟨t, mm, P, φ, he, ww, e, hspec⟩
  obtain ⟨algR, halg, y₀, yR, hfr, hchg⟩ := exists_dvr_frPt h1 h2 E H Dw l Xo c (c.V Wl) (c.V Wl).subtype Yw Tv ϖ
    (io.comp (algebraMap c.F K₁)) M.b M.aw χ W M.ρ M.ew M.thw hϖ
    (RingHom.ext fun x => (M.b_eq x).symm) M.ρ_eq hbase hgen (mono_spMap_subtype _) hpush (hbas χ W) M.thw_nz
  have hle : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := by
    intro v
    by_cases hv : algebraMap Tv.V Tv.Fr v = 0
    · rw [hv, map_zero, norm_zero]
      exact zero_le_one
    · rw [hn _ hv]
      exact zpow_le_one₀ Z.r_pos Z.r_lt.le (finLocal_vV_nonneg hv)
  have hlt : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1 := by
    rw [hn _ ((map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ.ne_zero)]
    exact zpow_lt_one₀ Z.r_pos Z.r_lt (finLocal_vV_pos hϖ)
  let Dv : DvrFrame d w Z :=
    { Tv := Tv, io := io, ιT := ιT, ιT_io := hc, norm_le := hle, ϖ := ϖ, ϖ_irr := hϖ, norm_ϖ := hlt
      algR := algR
      algW := ((arcι Dw Tv.Fr).comp ((PowerSeries.C (R := Tv.Fr)).comp (io.comp (algebraMap c.F K₁)))).toAlgebra
      algW_eq := fun _ => rfl
      yR := yR }
  have htan : ∀ τ k, GtTanR (d.e τ k) := fun τ k => by
    obtain ⟨e₁, e₂, -, l₂, t₁, hc⟩ := M.e_tie
    exact FinLocalTan.gtTanR_of_letBC (l₂ τ k) (FinLocalTan.gtTanR_of_gtComb (hc τ k) (t₁ τ))
  obtain ⟨ζ, N, hN, hζ, hnorm', -⟩ := exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  have hnorm := hnorm' htan
  have hAB : ∀ τ, A τ * (A τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ))
  have hbc : BcRigidAt Dv (io ζ * M.γ) lam (fun τ => (A τ)⁻¹) :=
    GlobalTheory.ArcRigidity.bcRigidAt_of_intModel h1 h2 hU h5 E H Dw l Xo c K₁ d w Z Dv Wl Yw M χ W y₀ ζ lam A (fun τ => (A τ)⁻¹) hob hnorm hbase
      halg hfr hchg hγ.1 (fun τ k => (hlam τ k).1) hAB hg
  have hmono : Mono Yw.j := by
    have := mono_spMap_subtype (c.V Wl)
    have := Yw.jQ_open
    unfold Model.j
    infer_instance
  have hrec : RecordAt Dv (intAt Xo c a n la) :=
    recordAt_of_isArcFr h1 h2 E H Dw l Xo c hev K₁ d w Z Dv (c.V Wl) (c.V Wl).subtype Yw M.b M.aw χ W M.ρ M.ew M.thw y₀ la eL
      hs hola M.ρ_eq halg hpush (hbas χ W) M.thw_nz hmono hfr hchg a n
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hζ
    exact zero_ne_one hζ
  have hζ1 : ‖ιT (io ζ)‖ = 1 := by
    have : ‖ιT (io ζ)‖ ^ N = 1 := by
      rw [← norm_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this
  refine (GlobalTheory.ArcQ.FrameCut.frame_of_cut h1 h2 E H Dw l Xo c hev K₁ d w a n (intAt Xo c a n la) (fun F hF => hF.1)).2 vth vη m
    ⟨Z, Dv, io ζ * M.γ, lam, A, fun τ => (A τ)⁻¹, ⟨mul_ne_zero ((map_ne_zero io).2 hζ0) hγ.1, ?_⟩,
      fun τ k => ⟨(hlam τ k).1, ?_⟩, ⟨hAB, fun τ k l => ?_⟩, hbc, hrec⟩
  · change ‖ιT (io ζ * M.γ)‖ = _
    rw [map_mul, norm_mul, hζ1, one_mul, hn _ hγ.1, hγ.2]
  · change ‖ιT (lam τ k)‖ = _
    rw [hn _ (hlam τ k).1, (hlam τ k).2]
  · change ‖ιT (A τ k l)‖ ≤ _
    by_cases h0 : A τ k l = 0
    · rw [h0, map_zero, norm_zero]
      exact (zpow_pos Z.r_pos _).le
    · rw [hn _ h0]
      exact zpow_le_zpow_right_of_le_one₀ Z.r_pos Z.r_lt.le ((hA τ k l).resolve_left h0)

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HolomorphicArc

theorem main : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  intro L₁ L₂ hU E _ _ _ H D l Xo c O _ β Y bF _ _ a χ W g ty Fu _ hty hrz hχ hgen
  letI := H.starRing
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  haveI : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨Λ⟩ := GlobalTheory.ArcModel.nonempty_gtAn L₁ L₂ hU E H D l c O β _ a
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_chain_arc_witness_universal_family L₁ L₂ E H D l Xo c O β Y bF a χ W Λ hχ hgen
  choose laA hA using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.A l.A_pos).1 (a.etaA v)
  choose laM hM using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.M (le_trans (by norm_num) l.three_le)).1 (a.eta v)
  obtain ⟨levA, levM⟩ := GlobalTheory.ArcPts.chain_levels L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C laA laM hA hM
  have hfin : AnFin Λ.A := (GlobalTheory.ArcThetaSpaces.sections_theta L₁ L₂ E H D l c O β _ a Λ).2.1
  have hover : (C.yF ≫ pullback.fst _ _) ≫ Xo.s =
      spMap ((algebraMap ℂ ℂ⸨X⸩).comp (bF.comp (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.yF_over, ← spMap_comp]
  have hrat : C.Φ.Rational := GlobalTheory.ConstRational.rational L₁ L₂ E H D l Xo Λ.A _ _ C.Φ laA laM hfin hover levA levM
  obtain ⟨Γ⟩ := _root_.GlobalTheory.GermRing.germs_spec.1
  obtain ⟨Ψ⟩ := GlobalTheory.ArcPts.Special.specPts_nonempty L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ _ Xo.s _ hover hfin hrat
  obtain ⟨lin, cst, hfac, hEF⟩ := GlobalTheory.ArcPts.exists_isFactor _ Λ.A
  obtain ⟨T₁, hT₁, hol, hfib⟩ :=
    GlobalTheory.SpecFibre.specPts_isFibAt L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat lin cst hfac
  obtain ⟨TA, -, hlA⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.A
  obtain ⟨TM, -, hlM⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.M
  have hdim := GlobalTheory.ArcPts.finrank_V_eq L₁ L₂ E H D l c O β _ a Λ g ty hty hrz
  have hol' : IsHolTo {w : ℂ | max T₁ (max TA TM) < w.im} Ψ.yw := isHolTo_halfPlane_mono (le_max_left _ _) hol
  obtain ⟨K, -⟩ := GlobalTheory.ArcPts.exists_cmp L₁ L₂ E H D l Xo _ g ty Fu Λ.A lin cst (max T₁ (max TA TM)) Ψ.yw Ψ.pi Ψ.fr laA laM
    rfl hEF hdim hol' (by
      intro w hw
      simp only [max_lt_iff] at hw
      obtain ⟨h₁, h₂, h₃⟩ := hw
      refine ⟨?_, hfib w h₁, fun hs => ⟨fun v => hlA w h₂ hs (hfib w h₁).per _ _ ?_ (levA v),
        fun v hv => hlM w h₃ hs (hfib w h₁).per _ _ ?_ (levM v hv)⟩⟩
      · rw [Ψ.yw_eq w (hT₁.trans_lt h₁)]
        exact over_of_generic _ _ _ _ _ (by rw [Ψ.yT_gen]; exact hover)
      · rw [← map_nsmul_eq_pow _ Xo.univ.etaA_add, Xo.univ.etaA_ker]
      · rw [← map_nsmul_eq_pow _ Xo.univ.eta_add, Xo.univ.eta_ker _ (nsmul_mem v)])
  exact GlobalTheory.ArcPts.nonempty_holArc L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib

end GlobalTheory.HolomorphicArc
end
end

