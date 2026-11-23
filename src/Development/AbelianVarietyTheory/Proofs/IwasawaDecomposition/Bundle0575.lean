module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesFourthPowerAssociated
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

def cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (q ⁻¹ᵁ ⊤) z trivial).hom.comp ((q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem cst_eq_cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) :
    cst q z a = cstHom q z a :=
  gs_eq q z ⊤ trivial _

theorem cst_inj {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {a b : R}
    (h : cst (p ≫ jK R) z a = cst (p ≫ jK R) z b) : a = b := by
  by_contra hne
  have hu := IntegralExpansionLocal.isUnit_cst_of_ne_zero p z (sub_ne_zero.2 hne)
  rw [cst_eq_cstHom, map_sub, ← cst_eq_cstHom, ← cst_eq_cstHom, h, sub_self] at hu
  exact not_isUnit_zero hu

theorem gm_top {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : ⊤ ≤ V) (g : Γ(Spec (CommRingCat.of R), V)ˣ) : ∃ u : Rˣ, (gm q z V g).val = cst q z (u : R) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom (res hV g), ?_⟩
  rw [← gm_res q z hV trivial g, ← gs_unit q z ⊤ trivial]
  simp only [cst, Units.coe_map, MonoidHom.coe_coe]
  congr 1
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom _
  rw [Iso.hom_inv_id]
  rfl

theorem gm_of_top {Z X : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (x : Spec (CommRingCat.of R) ⟶ X)
    {f : Z ⟶ X} (hf : f = q ≫ x) {V : X.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V) (g : Γ(X, V)ˣ) :
    ∃ u : Rˣ, (gm f z V g).val = cst q z (u : R) := by
  subst hf
  rw [← gm_pull q x z V (hV trivial) g]
  exact gm_top q z hV _

end GlobalTheory.PsiFourthCoord

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem val_psi_of_coord (D : DegPre R) (χ : D.X) {r : R} {j : PUnit → D.P.L.ι}
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
    {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : J (p ≫ D.xK χ) = j PUnit.unit) : (val (D.psi χ) p z J).val = cst (p ≫ jK R) z r := by
  have m₁ : p z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := h trivial
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  rw [val_of (D.psi χ) p z J j (fun _ => hJ)]
  refine (gs_unit p z _ m₁ _).symm.trans ((gs_res p z h trivial _).symm.trans ?_)
  refine (congrArg (gs p z _) e.symm).trans ((gs_pull p (jK R) z ⊤ trivial _).trans ?_)
  rw [hto]; rfl

theorem val_famMult_two {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 2 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul]

theorem val_rigK_of_top (D : DegPre R) {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J)
    (h : ⊤ ≤ (eSec D.P.A) ⁻¹ᵁ D.P.L.U (J ((p ≫ jK R) ≫ eSec D.P.A))) :
    ∃ u : Rˣ, (val D.rigK p z J).val = cst (p ≫ jK R) z u := by
  have e1 : p ≫ (toUnit (TK R)).left = p ≫ jK R := by
    congr 1
  rw [DegPre.rigK, val_pull hJ, e1]
  rw [val_of D.rig (p ≫ jK R) z J (fun _ => J ((p ≫ jK R) ≫ eSec D.P.A)) (fun _ => rfl)]
  exact gm_top _ z (fun y _ => Set.mem_iInter.2 fun _ => h trivial) _

theorem exists_good_pts (P : PolAV (Spec (CommRingCat.of R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {Z : Scheme.{0}} (t : Z ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of F) ⟶ Z) (ha : a ≫ t = DegPre.jFR F)
    (z : Z) (pk : (Spec (CommRingCat.of R) ⟶ P.A.left) → P.L.ι)
    (hpk : ∀ q, q ≫ P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ P.L.U (pk q)) :
    ∃ J, Good P.L z J ∧ ∀ q, q ≫ P.A.hom = 𝟙 _ → J (t ≫ q) = pk q := by
  obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB z (K := {q : Spec (CommRingCat.of R) ⟶ P.A.left // q ≫ P.A.hom = 𝟙 _})
    (fun q => t ≫ q.1) (fun q => pk q.1) (fun a' b' h => by
      have : a'.1 = b'.1 := GC.vpt_ext F P a'.2 b'.2 (by rw [← ha, Category.assoc, Category.assoc, h])
      rw [this]) (fun q => hpk q.1 q.2 trivial)
  exact ⟨J, hJ, fun q hq => e ⟨q, hq⟩⟩

end GlobalTheory.PsiFourthCoord


open GlobalTheory.PsiFourthCoord ReciprocityTheory.ChartRestriction.G.DVR in
theorem GlobalTheory.psi_coord_fourth_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ D D' Φ w _ nu mu z H r r' hr hr'
  classical
  set π := (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) with hπdef
  have hπ : π ≫ jK R = (DegPre.BF D.toPre (FractionRing R)).hom :=
    (Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A))
  have za : (DegPre.zF D.toPre (FractionRing R)).left ≫ (π ≫ jK R) = DegPre.jFR (FractionRing R) := by
    rw [hπ]; exact Over.w (DegPre.zF D.toPre (FractionRing R))
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨j', hj', h', e'⟩ := hr'
  choose pk hpk using fun q : Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left => GC.exists_chart_top D.toPre.P.L D.toPre.P.isLB q
  choose pk' hpk' using fun q : Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left =>
    GC.exists_chart_top D'.toPre.P.L D'.toPre.P.isLB q
  let pkD : (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun q =>
    if q = (D.toPre.c nu).left then j PUnit.unit else pk q
  let pkD' : (Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι := fun q =>
    if q = (D'.toPre.c mu).left then j' PUnit.unit else pk' q
  have hpkD : ∀ q, q ≫ D.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D.toPre.P.L.U (pkD q) := fun q _ => by
    by_cases hq : q = (D.toPre.c nu).left
    · subst hq; simp only [pkD, if_pos rfl]; exact hj
    · simp only [pkD, if_neg hq]; exact (hpk q).ge
  have hpkD' : ∀ q, q ≫ D'.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D'.toPre.P.L.U (pkD' q) := fun q _ => by
    by_cases hq : q = (D'.toPre.c mu).left
    · subst hq; simp only [pkD', if_pos rfl]; exact hj'
    · simp only [pkD', if_neg hq]; exact (hpk' q).ge
  obtain ⟨J, hJ, eJ⟩ := exists_good_pts D.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD hpkD
  obtain ⟨J', hJ', eJ'⟩ := exists_good_pts D'.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD' hpkD'
  have HH := H J J' hJ hJ'
  have pc : ∀ {X : Over (Spec (CommRingCat.of R))} (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X),
      x.left ≫ X.hom = 𝟙 _ := fun x => Over.w x
  have hc : (D.toPre.c nu).left ≫ D.toPre.P.A.hom = 𝟙 _ := pc _
  have hc' : (D'.toPre.c mu).left ≫ D'.toPre.P.A.hom = 𝟙 _ := pc _
  have he : eSec D.toPre.P.A ≫ D.toPre.P.A.hom = 𝟙 _ := pc η[D.toPre.P.A]
  have he' : eSec D'.toPre.P.A ≫ D'.toPre.P.A.hom = 𝟙 _ := pc η[D'.toPre.P.A]
  have hcΦ : ((D'.toPre.c mu).left ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact hc'
  have heΦ : (eSec D'.toPre.P.A ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact he'
  have V1 := val_psi_of_coord D.toPre nu h e π z J (by
    rw [show π ≫ D.toPre.xK nu = (π ≫ jK R) ≫ (D.toPre.c nu).left from (Category.assoc _ _ _).symm, eJ _ hc]
    simp only [pkD, if_pos rfl])
  have V1' := val_psi_of_coord D'.toPre mu h' e' π z J' (by
    rw [show π ≫ D'.toPre.xK mu = (π ≫ jK R) ≫ (D'.toPre.c mu).left from (Category.assoc _ _ _).symm, eJ' _ hc']
    simp only [pkD', if_pos rfl])
  obtain ⟨a, V2⟩ := val_rigK_of_top D.toPre π z J hJ (by rw [eJ _ he]; exact hpkD _ he)
  obtain ⟨a', V2'⟩ := val_rigK_of_top D'.toPre π z J' hJ' (by rw [eJ' _ he']; exact hpkD' _ he')
  have hψ : (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
      (π ≫ jK R) ≫ (D'.toPre.c mu).left := by
    rw [hπ, cP, Over.comp_left]; rfl
  have hψ1 : (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = (π ≫ jK R) ≫ eSec D'.toPre.P.A := by
    rw [hπ]; rfl
  have O1 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left ≫ Φ.hom.left) =
        pkD ((D'.toPre.c mu).left ≫ Φ.hom.left) := by rw [hψ, Category.assoc]; exact eJ _ hcΦ
    have k2 : J' (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
        pkD' (D'.toPre.c mu).left := by rw [hψ]; exact eJ' _ hc'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (D'.toPre.c mu).left hψ (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ hcΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ hc' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  have O2 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left ≫ Φ.hom.left) =
        pkD (eSec D'.toPre.P.A ≫ Φ.hom.left) := by rw [hψ1, Category.assoc]; exact eJ _ heΦ
    have k2 : J' (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = pkD' (eSec D'.toPre.P.A) := by
      rw [hψ1]; exact eJ' _ he'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (eSec D'.toPre.P.A) hψ1 (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ heΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ he' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  obtain ⟨b, O1⟩ := O1
  obtain ⟨b', O2⟩ := O2
  rw [val_famMult_two D'.tau_bimult _ hJ', val_famMult_two D.tau_bimult _ hJ] at HH
  set Ωc := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left
  set Ω1 := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left
  have HH2 : (val (D'.toPre.psi mu) π z J' ^ 2 * val D'.toPre.rigK π z J' ^ 2) ^ 2 * Ω1 ^ 2 =
      Ωc ^ 2 * (val (D.toPre.psi nu) π z J ^ 2 * val D.toPre.rigK π z J ^ 2) ^ 2 := by
    rw [HH, mul_pow, inv_pow, mul_right_comm, inv_mul_cancel_right]
  have V := congrArg Units.val HH2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at V
  rw [V1, V1', V2, V2', O1, O2] at V
  have V' : cst (π ≫ jK R) z (r' ^ 4 * ((a' : R) ^ 4 * (b' : R) ^ 2)) =
      cst (π ≫ jK R) z ((b : R) ^ 2 * (a : R) ^ 4 * r ^ 4) := by
    simp only [cst_eq_cstHom, map_mul, map_pow] at V ⊢
    linear_combination V
  have hR := cst_inj π z V'
  refine ⟨(b ^ 2 * a ^ 4) * (a' ^ 4 * b' ^ 2)⁻¹, ?_⟩
  have k : r ^ 4 * ((b ^ 2 * a ^ 4 : Rˣ) : R) = r' ^ 4 * ((a' ^ 4 * b' ^ 2 : Rˣ) : R) := by
    push_cast
    linear_combination -hR
  rw [Units.val_mul, ← _root_.mul_assoc, k, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigSymBaseChange

theorem rigidified_and_sym_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  intro S S' f G _ B _ β gp L σ hσ
  refine ⟨PolBaseChange.rigidified_pull gp ⟨L.rig, L.rigGen⟩, fun _ => ⟨⊤, trivial, ?_⟩⟩
  refine gen_chartPull (chartPullLinComb L.L β (K := Fin 2) _
    ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1] ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) fun k => ?_) σ hσ
  fin_cases k
  · show ((B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ (GrpObj.inv : G ⟶ G).left
    rw [Category.assoc, PolBaseChange.inv_comm gp, Category.assoc]
  · show (B.hom ⁻¹ᵁ ⊤).ι ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ 𝟙 G.left
    rw [Category.comp_id]

end GlobalTheory.RigSymBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Sub

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def LinOnCells (φ χ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → χ.LinearOn γ

def Subordinate (φ' φ : InvFun O) : Prop :=
  ∀ χ : InvFun O, LinOnCells bar q φ χ → LinOnCells bar q φ' χ

def SimpLab (φ lab : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ k : ℕ, 0 < k → lab.evalZ ((k : ℤ) • β) = lab.evalZ β) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), IsCell bar φ δ ∧ LinearIndependent ℤ δ ∧
        Function.Injective (fun i => lab.evalZ (δ i)) ∧
        ∀ j, ∃ a : Fin m' → ℝ, (∀ i, 0 ≤ a i) ∧ toReal (γ j) = ∑ i, a i • toReal (δ i)

variable {bar q}

theorem linOnCells_self (φ : InvFun O) : LinOnCells bar q φ φ := fun _ _ _ _ _ _ _ _ h => h.linear

theorem Subordinate.refl (φ : InvFun O) : Subordinate bar q φ φ := fun _ h => h

theorem Subordinate.trans {φ'' φ' φ : InvFun O} (h₁ : Subordinate bar q φ'' φ') (h₂ : Subordinate bar q φ' φ) :
    Subordinate bar q φ'' φ := fun χ h => h₁ χ (h₂ χ h)

theorem Subordinate.linearOn {φ' φ : InvFun O} (h : Subordinate bar q φ' φ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ' γ) : φ.LinearOn γ :=
  h φ (linOnCells_self φ) X hX m γ hγ

end Sub

section Inhab

def zeroFun (O : Type) [CommRing O] : InvFun O where
  toFun _ _ := 0
  inv _ _ _ _ _ := rfl
  zero _ := rfl

@[simp] theorem zeroFun_evalZ {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (β : LinearMap.BilinForm ℤ X) : (zeroFun O).evalZ β = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  simp only [InvFun.evalZ, (zeroFun O).eval_eq hr]
  rfl

end Inhab

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem step {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {ι : Type} [Finite ι]
    {m k : ι → ℕ} (S : Fr M m k) (hM : Good M d) (τ : ι) (hk : k τ < m τ) (k' : ι → ℕ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z)
      (S' : Fr M' m k'), Good M' (d + (m τ - k τ - 1)) ∧ Refines S S' φ f := by
  obtain ⟨A₀, hA₀⟩ := S.nonempty (genericPoint M.Z)
  obtain ⟨EE, hE⟩ := GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock F Ω M ι m k S τ A₀ hA₀
  have : Nonempty (Rest m k τ) := ⟨⟨⟨k τ, hk⟩, le_rfl⟩⟩
  obtain ⟨Ω', _, _, M', φ, f, s, hP, hpr⟩ := _root_.GlobalTheory.FlagBundle.exists_projBundle F Ω M _ EE hM.1
  have hc : Fintype.card (Rest m k τ) = m τ - k τ := by
    rw [Fintype.card_subtype, ← Fin.card_Ici ⟨k τ, hk⟩]
    exact congrArg _ (Finset.ext fun j => by simp [Fin.le_def])
  have hA := GlobalTheory.T.isAffineSpaceCoveredMorphism F Ω Ω' M M' φ f _ EE s hP
  rw [hc] at hA
  have hp := _root_.GlobalTheory.FlagBundle.projPoints_of_projBundle F Ω Ω' M M' φ f _ EE s hP
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine F Ω Ω' M M' φ f ι m k k' S τ hk A₀ EE s h1 h2 hA₀ hE hp
  refine ⟨Ω', _, _, M', φ, f, S', ⟨hpr, GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add F Ω Ω' M M' φ f _ d hA hM.2.1, _root_.GlobalTheory.FlagBundle.AffCover.geometricallyIntegral F Ω Ω' M M' φ f _ hA hM.2.2⟩,
    fun τ' => ?_, hP.hom, fun z' A' hA' => ?_, GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered F Ω Ω' M M' φ f _ hA,
    GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement F Ω Ω' M M' φ f ι m k k' S S' τ hk A₀ EE s h1 h2 hA₀ hE hp hS'⟩
  · by_cases h : τ' = τ
    · subst h; exact h1 ▸ Nat.le_succ _
    · exact (h2 τ' h).ge
  · rw [hS'] at hA'
    exact hA'.1

theorem tower {F : Type} [Field F] {ι : Type} [Fintype ι] {m : ι → ℕ} (n : ℕ) :
    ∀ {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {k : ι → ℕ} (S : Fr M m k), Good M d → k ≤ m →
      ∑ τ, (m τ - k τ) = n → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m m),
        Y.dim = d + ∑ τ, (m τ - k τ).choose 2 ∧ Refines S S' φ f := by
  classical
  induction n with
  | zero =>
    intro Ω _ _ M d k S hM hk hn
    obtain rfl : k = m := funext fun τ => le_antisymm (hk τ)
      (Nat.sub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hn τ (Finset.mem_univ _)))
    obtain ⟨Y, φ, f, S', h1, h2⟩ := GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel F Ω M d ι k k S hM
    exact ⟨Y, φ, f, S', by simpa using h1, h2⟩
  | succ n ih =>
    intro Ω _ _ M d k S hM hk hn
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hτ' : k τ < m τ := by omega
    let k' := Function.update k τ (k τ + 1)
    have h1 : k' τ = k τ + 1 := Function.update_self _ _ _
    have h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ' := fun τ' h => Function.update_of_ne h _ _
    obtain ⟨Ω', _, _, M', φ, f, S', hM', hR⟩ := step M d S hM τ hτ' k' h1 h2
    have key : ∀ g : ℕ → ℕ, ∑ t, g (m t - k' t) + g (m τ - k τ) = ∑ t, g (m t - k t) + g (m τ - k τ - 1) := fun g => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ), ← Finset.add_sum_erase _ (fun t => g (m t - k t)) (Finset.mem_univ τ),
        h1, Finset.sum_congr rfl fun t ht => by rw [h2 t (Finset.ne_of_mem_erase ht)], Nat.sub_add_eq]
      ring
    obtain ⟨Y, φ', f', S'', hd, hR'⟩ := ih M' _ S' hM' (fun t => by
      by_cases h : t = τ
      · subst h; rw [h1]; exact hτ'
      · rw [h2 t h]; exact hk t) (by have := key id; simp only [id] at this; omega)
    refine ⟨Y, φ'.comp φ, f' ≫ f, S'', ?_, _root_.GlobalTheory.FlagBundle.refines_comp F Ω Ω' M M' φ f Y.Fn (ratOf Y) φ' f' ι m k k' m S S' S'' hR hR'⟩
    have := key fun a => a.choose 2
    obtain ⟨a, ha⟩ : ∃ a, m τ - k τ = a + 1 := ⟨m τ - k τ - 1, by omega⟩
    rw [ha, Nat.choose_succ_succ' a 1, Nat.choose_one_right, Nat.add_sub_cancel] at this
    rw [hd, ha, Nat.add_sub_cancel]
    simp only [Nat.reduceAdd] at this
    omega

open _root_.CategoryTheory.Limits NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
  {F : Type} [Field F] (e : F ≃+* c.F)

theorem genericPoint_mem {B : Scheme.{0}} [IsIntegral B] (j : B ⟶ gen Z) [IsOpenImmersion j] :
    j (genericPoint B) ∈ Set.range Z.jQ := by
  have := Z.jQ_open
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Z.jQ_dense.inter_open_nonempty _ j.isOpenEmbedding.isOpen_range ⟨_, genericPoint B, rfl⟩
  exact ((genericPoint_specializes b).map j.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hb

theorem exists_flagCpt (hS : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    [IsOpenImmersion j] (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) :
    ∃ (C : FlagCpt Z e) (f : C.Y.X ⟶ B.X), C.π = f ≫ j ∧ C.Y.dim = B.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 ∧
      ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x →
        x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  have := Z.jQ_open
  obtain ⟨f₀, S, A₀, hT⟩ := _root_.GlobalTheory.ShFam.TieBase.exists_tied E H Dw l Xo c O β Z F e B j hj
  obtain ⟨Y, φ, f, S', hd, hR⟩ := tower _ (ratOf B) B.dim S (good_ratOf B) (fun _ => Nat.zero_le _) rfl
  change Y.X ⟶ B.X at f
  obtain ⟨g₀, A₁, hT', hC⟩ := _root_.GlobalTheory.ShFam.TieUp.main E H Dw l Xo c O β Z F e B Y j f₀ S A₀ _ S' φ f hT hR
  obtain ⟨gr, hgr⟩ := _root_.GlobalTheory.ShFam.GradedDiv.exists_gr E H Dw l Xo c O β Z F e Y (f ≫ j) g₀ S' A₁ hT'
  have hgen := genericPoint_mem Z j
  obtain ⟨D, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed (gen Z) B.X j (genBd Z) hS fun h => h hgen
  obtain ⟨D', hD1', hD2', hD3'⟩ := _root_.GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback F B Y φ f D hR.hom hR.rad hD1 hD3
  have hstr : (f ≫ j) ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [Category.assoc, hj]; exact hR.hom.inducedModelMorphism_comp_structureMap
  have hrange : Set.range (genericPt Y ≫ f ≫ j) ⊆ Set.range Z.jQ := by
    rintro _ ⟨w, rfl⟩
    have h : genericPt Y ≫ f = spMap φ.toRingHom ≫ genericPt B := hR.hom
    have h' : genericPt B (spMap φ.toRingHom w) = genericPoint B.X := (ratOf B).pt_apply _
    rw [← Category.assoc, h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h']
    exact hgen
  let z : Sp Y.Fn ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (genericPt Y ≫ f ≫ j) hrange
  have hz : z ≫ Z.jQ = genericPt Y ≫ f ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hzs : z ≫ pullback.snd _ _ = spMap (constF e Y) := by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    rw [← Z.jQ_over, ← Category.assoc, hz, ← Category.comp_id (pullback.snd Z.s (spMap β)), ← h2]
    refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h1).trans (Spec.map_comp _ _).symm)
    rw [← hstr]
    simp only [Category.assoc]
  obtain ⟨y0, hy1, hy2⟩ := GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame E H Dw l Xo c O β Z Y.Fn (constF e Y) z _ g₀ hzs (by
    rw [← Category.assoc, hz]; simp only [Category.assoc])
  let C : FlagCpt Z e :=
    { Y := Y, π := f ≫ j, π_str := hstr, y0 := y0, f0 := g₀, y0_x := by rw [hy1, hz], flagComponentFramedPoint_frame := by rw [hy1]; exact hy2, gr := gr,
      gr_spec := hgr, bd := D', bd_eff := hD1', bd_red := hD3'
      bd_supp := fun y => (hD2' y).trans ((hD2 _).trans (by rw [Scheme.Hom.comp_apply])) }
  exact ⟨C, f, rfl, by simpa using hd,
    _root_.GlobalTheory.ShFam.flagex_lifts E H Dw l Xo c O β Z F e C B j f₀ S A₀ S' A₁ φ f hj rfl hT hT' hC hR⟩

end Component

end GlobalTheory.FlagBundle
end
end

