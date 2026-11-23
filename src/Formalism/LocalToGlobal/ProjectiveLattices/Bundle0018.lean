module

public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfV
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.LieAlg
public import Formalism.LocalToGlobal.ProjectiveLattices.LieRel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions

def DatDom (D : D7) (j : ℕ) (hI : DatInt D j) : Prop := DomFor D j (efW D j hI)

def datumOfRecord (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (hP : FactPrincipalDatum)
    (hd : DatDom D j (datInt_of hP D j)) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum (hostOfRecord D) :=
  datumOf D j (datInt_of hP D j)
    { unimod := efW_unimod_of hP D j _, rank := latW_rank D j hj, dom := hd }

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem gfp_chart_iso {R : Type} [CommRing R] {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [GrpObj G₂]
    (e : G₁ ≅ G₂) [IsMonHom e.hom] {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ G₁} (hx : IsUnivChart G₁ n xc) :
    IsUnivChart G₂ n (fun m => xc m ≫ e.hom) := by
  have h1 : ∀ X : Over (Spec (CommRingCat.of R)), (1 : X ⟶ G₁) ≫ e.hom = 1 := by
    intro X
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, hx.1 m]
  · rw [← Category.assoc, hx.2.1 m, h1]
  · intro A _ _ aug m hker y hy
    have hy' : ReciprocityTheory.ChartRestriction.G.Chart.spMap aug ≫ (y ≫ e.inv) = 1 := by
      rw [← Category.assoc, hy, ← h1, Category.assoc, e.hom_inv_id, Category.comp_id]
    obtain ⟨ψ, hψ, huniq⟩ := hx.2.2 A aug m hker (y ≫ e.inv) hy'
    refine ⟨ψ, ⟨hψ.1, ?_⟩, fun ψ' hψ' => huniq ψ' ⟨hψ'.1, ?_⟩⟩
    · rw [← Category.assoc, ← Iso.comp_inv_eq, hψ.2]
    · rw [Iso.comp_inv_eq, hψ'.2, Category.assoc]

def gfpEig {L : Type} [Field L] [Algebra c.F L] {x : Sp L ⟶ Xo.X} {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
    (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) : Submodule L (Fin n → L) :=
  eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a))

section BC

variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gfpVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gfpVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gfpVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  have ht : tvec (x := xc) (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc).symm
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx
        (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a)) _).symm
  have e1 : ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    simp
    all_goals first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  simp only [gfpVec, ht, Over.comp_left, Category.assoc, e1]

theorem gfp_bc {L' : Type} [Field L'] [Algebra L L'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L') (ReciprocityTheory.ChartRestriction.G.Chart.JetR L' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap L L') ≫ x)).obj Xo.univ.t.G) (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, gfpVec (spMap (algebraMap L L') ≫ x) xc' (algebraMap L L' ∘ cc) =
        spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc cc) ∧
      ∀ (a : 𝓞 E) (cc : Fin n → L),
        tmap hx' ((Over.pullback (spMap (algebraMap L L') ≫ x)).map (Xo.univ.t.act.act a)) (algebraMap L L' ∘ cc) =
          algebraMap L L' ∘ tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := L) (R' := L') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB L L'))
    (isGrpPullback_pullback Xo.univ.t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback Xo.univ.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB L L' ≫ x))
  have hv : ∀ cc : Fin n → L, gfpVec (spMap (algebraMap L L') ≫ x) (fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc) =
      spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc cc := by
    intro cc
    have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left =
        (tvec (x := x₁) (algebraMap L L' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  have hx' := gfp_chart_iso e hx₁
  refine ⟨fun m => x₁ m ≫ e.hom, hx', hv, fun a cc => gfp_inj hx' ?_⟩
  rw [gfpVec_tmap hx', hv, hv, gfpVec_tmap hx, Category.assoc]

variable [Algebra c.F L]

theorem gfp_finrank (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Module.finrank L (gfpEig (c := c) hx τ) = Dw.mult τ := by
  classical
  obtain ⟨xc', hx', -, htm⟩ := gfp_bc (L' := AlgebraicClosure L) hx
  have hrank := ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := L) (k := AlgebraicClosure L)
    (fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)))
    (fun a => tmap hx' ((Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a)))
    htm (fun a => algebraMap c.F L (embK c τ a))
  let β : KA l →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp
    ((algebraMap c.F L).comp (IntermediateField.inclusion c.le).toRingHom)
  have hβ : (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) ≫ Xo.s = spMap β := by
    rw [Category.assoc, hx0]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hd := (Xo.univ.geom (AlgebraicClosure L) _ β hβ).1
  let τ' : 𝓞 E →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp ((algebraMap c.F L).comp (embK c τ))
  have key : ∀ N, LieMult Xo.univ.t.act (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) τ' N →
      Module.finrank (AlgebraicClosure L) (eigLat hx'
        (fun a => (Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a))
        (fun a => τ' a)) = N :=
    fun N h => ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult gfp_hcId (Category.comp_id _) hx' Xo.univ.t.act
      Xo.univ.t.act.act (fun a => by rw [Category.comp_id, Category.id_comp]) _ (fun a => rfl) τ' h
  have hinj : Function.Injective ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) := RingHom.injective _
  have e0 : τ' H.rt = β (baseKA l).ρ ↔ τ (H.rt : E) = H.rt0 := by
    constructor
    · intro h
      have h' := @hinj (embK c τ H.rt) (IntermediateField.inclusion c.le (baseKA l).ρ) h
      exact congrArg (fun z : c.F => (z : ℂ)) h'
    · intro h
      have h' : embK c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext h
      exact congrArg ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) h'
  refine hrank.trans ?_
  unfold Datum.mult
  split_ifs with h
  · exact key _ ((hd τ').1 (e0.2 h))
  · exact key _ ((hd τ').2 (fun h' => h (e0.1 h')))

theorem gfp_basis (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ)
    (d : Fin (Dw.mult τ) → Fin n → L) (hd : LinearIndependent L d) (hdW : ∀ i, d i ∈ gfpEig (c := c) hx τ)
    (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (he : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → L, IsCombAt x (fun i => gfpVec x xc (d i)) a w := by
  obtain ⟨cc, rfl⟩ := gfp_exists hx w hw
  have hcc : cc ∈ gfpEig (c := c) hx τ := (gfp_eig_iff hx τ cc).1 he
  have hle : Submodule.span L (Set.range d) ≤ gfpEig (c := c) hx τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hdW i
  have hfr : Module.finrank L (Submodule.span L (Set.range d)) =
      Module.finrank L (gfpEig (c := c) hx τ) := by
    rw [finrank_span_eq_card hd, Fintype.card_fin, gfp_finrank hx0 hx τ]
  have heq : Submodule.span L (Set.range d) = gfpEig (c := c) hx τ :=
    Submodule.eq_of_le_of_finrank_eq hle hfr
  have hspan : cc ∈ Submodule.span L (Set.range d) := heq ▸ hcc
  obtain ⟨a, ha⟩ : ∃ a : Fin (Dw.mult τ) → L, ∑ i, a i • d i = cc := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun L).1 hspan
    | exact Submodule.mem_span_range_iff_exists_fun.1 hspan
  refine ⟨a, (gfp_comb_iff hx d a cc).2 ha.symm, ?_⟩
  intro a' ha'
  have h2 : cc = ∑ j, a' j • d j := (gfp_comb_iff hx d a' cc).1 ha'
  have h3 : ∑ j, a' j • d j = ∑ j, a j • d j := h2.symm.trans ha.symm
  funext i
  have h4 := Fintype.linearIndependent_iff.1 hd (a' - a) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h3, sub_self]) i
  simpa [sub_eq_zero] using h4

end BC

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA)
open Formalism.L2.Pj.LieRel Formalism.L2.Pj.LieAlg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem int_val (T : CDVR) (io : c.F →+* T.Fr) (τ : E →+* ℂ) (a : 𝓞 E) :
    ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) := by
  obtain ⟨p, hp, hpa⟩ := NumberField.RingOfIntegers.isIntegral a
  refine IsIntegrallyClosed.isIntegral_iff.1 ⟨p.map (Int.castRingHom T.V), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hf : (algebraMap T.V T.Fr).comp (Int.castRingHom T.V) =
      (io.comp (embK c τ)).comp (algebraMap ℤ (𝓞 E)) := RingHom.ext_int _ _
  rw [hf]
  have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ (𝓞 E)) (io.comp (embK c τ)) a
  rw [hpa, map_zero] at h3
  exact h3.symm


set_option maxHeartbeats 800000 in
theorem lieFree : LieFreeSt Xo c := by
  intro T io G t' x m1 m2 _ u₀ hu₀t hu₀e hu₀b
  let _ := io.toAlgebra
  have := G.semi.smooth
  have : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  obtain ⟨n, xc, hxc⟩ := univChartLoc G.G
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := T.V) (R' := T.Fr) G.G n xc hxc
  have hpt : ∀ cc : Fin n → T.V, pushR G.G (tvec (x := x') (algebraMap T.V T.Fr ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM0 : ∀ (a : 𝓞 E) (cc : Fin n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) =
        algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G.G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  have hM : ∀ (a : 𝓞 E) (cc : Fin n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) =
        fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j) := hM0
  have h1 := m1.cart
  have h2 : IsGrpPullback t'.G G.G (fB T.V T.Fr) m2.φ := m2.cart
  have hex : ∀ e : Fin n → T.Fr, ∃ v, RelA x m1.φ m2.φ v (tvec (x := x') e) :=
    fun e => relA_exists_v x h1 h2 (tvec (x := x') e)
  choose vA hvA using hex
  have coordA : ∀ w, IsTanAt x w → ∃ e : Fin n → T.Fr, (vA e).left = w := by
    intro w hw
    let v0 : epsAt x ⟶ Xo.univ.t.G := Over.homMk w hw.1
    obtain ⟨y0, hy0⟩ := relA_exists_y x h1 h2 v0
    have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y0 := (relA_tan x h1 h2 hy0).1 hw.2
    refine ⟨tcoord hx' y0 ht, ?_⟩
    exact congrArg (fun q => q.left) ((relA_uniq x h1 h2 (hvA _) hy0).2 (tcoord_spec hx' y0 ht).symm)
  have tanA : ∀ e, IsTanAt x (vA e).left := fun e =>
    ⟨Over.w (vA e), (relA_tan x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩
  have eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔
      ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e := by
    intro τ e
    unfold IsEigAt
    refine forall_congr' fun a => ?_
    rw [← tvec_eig_iff hx']
    exact relA_eig x h1 h2 (hvA e) (t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (m1.act a) (m2.act a) _
  have combA : ∀ {m : ℕ} (d : Fin m → Fin n → T.Fr) (cf : Fin m → T.Fr) (e : Fin n → T.Fr),
      IsCombAt x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i := by
    intro m d cf e
    have hr : ∀ i, RelA x m1.φ m2.φ (sclA x (cf i) ≫ vA (d i))
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x := x') (d i)) :=
      fun i => relA_scl x (hvA (d i)) (cf i)
    have hp := relA_prod x h1 h2 _ _ hr
    rw [prod_tvec hx'] at hp
    constructor
    · rintro ⟨u, hu, hw⟩
      have hu' : u = fun i => sclA x (cf i) ≫ vA (d i) := funext fun i => Over.OverMorphism.ext (hu i)
      subst hu'
      exact tvec_inj hx' ((relA_uniq x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))
    · rintro rfl
      exact ⟨fun i => sclA x (cf i) ≫ vA (d i), fun i => rfl,
        congrArg (fun q => q.left) ((relA_uniq x h1 h2 hp (hvA _)).2 rfl)⟩
  choose χ hχ using fun τ a => int_val c T io τ a
  have key : ∀ τ : E →+* ℂ, ∃ (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      (∀ i, IsTan (ub i)) ∧ (∀ i, IsEigV c io G τ (ub i)) ∧
      (∀ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) ∧
      (∀ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u i ∧
        u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub i).left) ∧
      (∀ i, IsTanAt x (u i)) ∧ (∀ i, IsEigAt c τ (u i)) ∧
      (∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x u a w) ∧
      ∀ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u i) := by
    intro τ
    choose v hv using fun i => coordA (u₀ τ i) (hu₀t τ i)
    have hu₀ : u₀ τ = fun i => (vA (v i)).left := funext fun i => (hv i).symm
    have eigM : ∀ e, IsEigAt c τ (vA e).left ↔
        ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = algebraMap T.V T.Fr (χ τ a) • e := by
      intro e
      rw [eigA τ e]
      simp only [hχ τ]
    have hvM : ∀ a i, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (v i) =
        algebraMap T.V T.Fr (χ τ a) • v i := fun a i => (eigM (v i)).1 (by rw [hv i]; exact hu₀e τ i) a
    have hbM : ∀ w, (∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) w =
        algebraMap T.V T.Fr (χ τ a) • w) → ∃! cf : Fin (Dw.mult τ) → T.Fr, w = ∑ i, cf i • v i := by
      intro w hw
      obtain ⟨cf, hcf, hu⟩ := hu₀b τ (vA w).left (tanA w) ((eigM w).2 hw)
      rw [hu₀] at hcf hu
      exact ⟨cf, (combA v cf w).1 hcf, fun cf' h' => hu cf' ((combA v cf' w).2 h')⟩
    obtain ⟨b, hbe, hbb, hbt⟩ := eig_basis (fun a => tmap hxc (G.act.act a)) (χ τ)
      (fun a => tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a))) hM v hvM hbM
    choose C hCd hCz hCb using hbt
    refine ⟨fun i => cvV (tvec (x := xc) (b i)), fun i => (vA (fun j => algebraMap T.V T.Fr (b i j))).left,
      fun i => isTan_cvV (isTan_tvec hxc (b i)), fun i a z hz => ?_, fun w hw he => ?_, fun i => ?_, fun i => tanA _,
      fun i => ?_, fun w hw he => ?_, fun i => ⟨C i, isUnit_iff_ne_zero.2 (hCd i), hCz i, ?_⟩⟩
    · have hz' : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      subst hz'
      exact (eigV_iff hxc (G.act.act a) (b i) _).2 (hbe a i)
    · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc hw
      have hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := fun a =>
        (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))
      obtain ⟨r, hr, hru⟩ := hbb cc hcc
      exact ⟨r, (comb_iff hxc b r cc).2 hr, fun r' h' => hru r' ((comb_iff hxc b r' cc).1 h')⟩
    · obtain ⟨w, hw, hwl⟩ := hvA (fun j => algebraMap T.V T.Fr (b i j))
      have hw' : w.left ≫ m2.φ = (tvec (x := x') (fun j => algebraMap T.V T.Fr (b i j))).left ≫
          pullback.fst G.G.hom (fB T.V T.Fr) := hw
      refine ⟨w.left, hwl.symm, ?_⟩
      rw [cvV_left]
      exact hw'.trans (hcomp (b i))
    · refine (eigA τ _).2 fun a => ?_
      rw [hM a (b i), hbe a i, ← hχ τ a]
      funext j
      simp [Pi.smul_apply, smul_eq_mul, map_mul]
    · obtain ⟨e, rfl⟩ := coordA w hw
      have hP : ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e =
          algebraMap T.V T.Fr (χ τ a) • e := (eigM e).1 he
      obtain ⟨d, hd, hdu⟩ := tri_basis (fun w => ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) w =
          algebraMap T.V T.Fr (χ τ a) • w) v hbM C hCz hCd e hP
      have hCb' : ∀ i, (∑ j, C i j • v j) = fun j => algebraMap T.V T.Fr (b i j) := fun i => (hCb i).symm
      simp only [hCb'] at hd hdu
      exact ⟨d, (combA _ d e).2 hd, fun d' h' => hdu d' ((combA _ d' e).1 h')⟩
    · rw [hu₀]
      exact (combA v (C i) _).2 (hCb i)
  choose ub u hub using key
  exact ⟨ub, u, ⟨fun τ i => (hub τ).1 i, fun τ i => (hub τ).2.1 i, fun τ w hw he => (hub τ).2.2.1 w hw he,
    fun τ i => (hub τ).2.2.2.1 i⟩, fun τ i => (hub τ).2.2.2.2.1 i, fun τ i => (hub τ).2.2.2.2.2.1 i,
    fun τ w hw he => (hub τ).2.2.2.2.2.2.1 w hw he, fun τ i => (hub τ).2.2.2.2.2.2.2 i⟩

end Formalism.L2.Pj
end
end

