module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamily
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNormU

theorem germ_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens)
    (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  apply Units.ext
  rw [gm_val (r ≫ q) z U h]
  show _ = (r.stalkMap z).hom (gm q (r z) U a).val
  rw [gm_val q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ U) z h _).symm

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B]

theorem zb_zb : zb A B ≫ zb A B = zb A B := by ext <;> simp [zb]
theorem zb_fst' : zb A B ≫ fst A B = fst A B := by simp [zb]
theorem fst_comp_lift_id_one_eq_prodSetSecondCoordZero : fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) = zb A B := by ext <;> simp [zb]

theorem rhoZ_rhoZ (q : A ⟶ A') : rhoZ (B := B) q ≫ rhoZ q = rhoZ q := by
  have e : (zb A B).left ≫ (zb A B).left = (zb A B).left := by rw [← Over.comp_left, zb_zb]
  apply pullback.hom_ext <;> simp [e]

theorem rhoZ_a (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_fst_assoc, ← Over.comp_left, zb_fst']

theorem rhoZ_a' (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_snd_assoc, ← Over.comp_left, zb_fst']

theorem a_s (q : A ⟶ A') : (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_fst, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

theorem pullbackSnd_fst_comp_lift_id_one (q : A ⟶ A') : (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_snd, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem germ_gen {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (τ : LB.Gen (L.pull F)) (hτ : τ.IsGen)
    (g : Y ⟶ X') (y : Y) (i i' : L.ι) (hi : F (g y) ∈ L.U i) (hi' : F (g y) ∈ L.U i') :
    gm g y _ (τ.s fun _ => i) = gm (g ≫ F) y _ (L.g i i') * gm g y _ (τ.s fun _ => i') := by
  have hp : g y ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  have e : gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i')) ((L.pull F).g (fun _ => i) (fun _ => i')) =
      gm (g ≫ F) y _ (L.g i i') := by
    show gm g y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g i i'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res g y _ hp _).trans (gm_pull g F y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _)
  have := congrArg (gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i'))) (hτ (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res g y _ hp, gm_res g y _ hp, e] at this
  exact this

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem pt_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e]; rfl

theorem rhoZ_rhoZ_apply {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ A') (z) :
    rhoZ (B := B) q (rhoZ q z) = rhoZ q z := pt_eq (rhoZ_rhoZ q) z


set_option maxHeartbeats 800000 in
theorem normalise : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (GlobalTheory.DescNorm.twist (q ▷ B).left P φ u) := by
  intro K _ A A' B _ _ q P τ hP hτ φ hφ
  let W : P.ι × P.ι → (pullback (q ▷ B).left (q ▷ B).left).Opens := fun p => rhoZ q ⁻¹ᵁ chart (q ▷ B).left P p.1 p.2
  have h2 : ∀ p, W p ≤ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.1) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (a_s q) z]; exact hz.1)
  have h3 : ∀ p, W p ≤ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.2) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz.2)
  let v : ∀ p, Γ(pullback (q ▷ B).left (q ▷ B).left, W p)ˣ := fun p =>
    (pullU (rhoZ q) _ (φ p.1 p.2))⁻¹ *
      (res (h2 p) (pullU (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.1)))⁻¹ *
      res (h3 p) (pullU (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.2))
  have hv : ∀ (Y : Scheme.{0}) (g : Y ⟶ pullback (q ▷ B).left (q ▷ B).left) (y : Y) (p : P.ι × P.ι), g y ∈ W p →
      gm g y (W p) (v p) = (gm (g ≫ rhoZ q) y _ (φ p.1 p.2))⁻¹ *
        (gm (g ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.1))⁻¹ *
        gm (g ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.2) := by
    intro Y g y p hy
    simp only [v, map_mul, map_inv]
    rw [gm_pull g (rhoZ q) y _ hy, gm_res g y (h2 p) hy, gm_pull g (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h2 p hy),
      gm_res g y (h3 p) hy, gm_pull g (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h3 p hy)]

  have indep : ∀ p p', ∀ z ∈ W p ⊓ W p', gm (𝟙 _) z (W p) (v p) = gm (𝟙 _) z (W p') (v p') := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hz, hz'⟩
    rw [hv _ (𝟙 _) z _ hz, hv _ (𝟙 _) z _ hz']
    simp only [Category.id_comp]
    have hz1 : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i := hz.1
    have hz2 : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j := hz.2
    have hz1' : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i' := hz'.1
    have hz2' : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j' := hz'.2
    have c1 : gm (rhoZ q) z _ (φ i' j') = gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') *
        gm (rhoZ q) z _ (φ i j) * gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) := by
      have e := congrArg (Units.map ((rhoZ q).stalkMap z).hom.toMonoidHom) (hφ (rhoZ q z) i i' j j' hz1 hz1' hz2 hz2')
      rw [map_mul, map_mul] at e
      have k1 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i' j') ⟨hz1', hz2'⟩ (φ i' j')
      have k2 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i j) ⟨hz1, hz2⟩ (φ i j)
      have k3 := germ_comp (rhoZ q) (pullback.fst (q ▷ B).left (q ▷ B).left) z (P.U i ⊓ P.U i') ⟨hz1, hz1'⟩ (P.g i i')
      have k4 := germ_comp (rhoZ q) (pullback.snd (q ▷ B).left (q ▷ B).left) z (P.U j' ⊓ P.U j) ⟨hz2', hz2⟩ (P.g j' j)
      rw [Category.comp_id] at k1 k2
      rw [k1, k2, k3, k4]
      exact e
    have t1 := germ_gen τ hτ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z i i'
      (by rw [pt_eq (a_s q) z]; exact hz1) (by rw [pt_eq (a_s q) z]; exact hz1')
    have t2 := germ_gen τ hτ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z j j'
      (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2) (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2')
    rw [a_s] at t1
    rw [pullbackSnd_fst_comp_lift_id_one] at t2
    have cc := gm_cocycle hP (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z hz2 hz2' hz2
    rw [gm_self hP _ z hz2] at cc
    rw [c1, t1, t2]
    generalize gm (rhoZ q) z _ (φ i j) = Φ
    generalize gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') = G₁
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) = G₂ at cc ⊢
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j j') = H at cc ⊢
    generalize gm (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => i') = T₁
    generalize gm (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => j') = T₂
    rw [eq_inv_of_mul_eq_one_left cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hc : (⊤ : (pullback (q ▷ B).left (q ▷ B).left).Opens) ≤ iSup W := fun z _ => by
    obtain ⟨i, hi⟩ := exists_chart hP (pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z))
    obtain ⟨j, hj⟩ := exists_chart hP (pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) hc v indep
  refine ⟨u, fun T r t i j hi hj => ?_⟩
  have hm : (r ≫ rhoZ q) t ∈ chart (q ▷ B).left P i j := ⟨hi, hj⟩
  have hw : (r ≫ rhoZ q) t ∈ W (i, j) := by
    show rhoZ q (rhoZ q (r t)) ∈ chart (q ▷ B).left P i j
    rw [rhoZ_rhoZ_apply]; exact hm
  show gm _ t _ (φ i j * res le_top u) = _
  rw [map_mul, gm_res _ t le_top hm, ← gm_res _ t (le_top : W (i, j) ≤ ⊤) hw u, hu (i, j), hv T (r ≫ rhoZ q) t (i, j) hw]
  simp only [Category.assoc, rhoZ_rhoZ, rhoZ_a, rhoZ_a']
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]

end GlobalTheory.DescNormU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTObjMap

theorem exists_objMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  intro p _ D R _ b N S₀ A₀ _ P₀ hP₀ T Z t₁ t₂ o u g πZ z φo φ₂o φu φ₂u ψ ho sqo io hu squ iu hz hψ hw hact heta
  have cart : IsGrpPullback o.A u.A z ψ := IsGrpPullback.cancel hu (by rw [hz, hψ]; exact ho) hw
  have wc : ((fst o.A o.A).left ≫ ψ) ≫ u.A.hom = ((snd o.A o.A).left ≫ ψ) ≫ u.A.hom := by
    rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A), Over.w (snd o.A o.A)]
  let φ₂ : (G2 o.A).left ⟶ (G2 u.A).left := pullback.lift ((fst o.A o.A).left ≫ ψ) ((snd o.A o.A).left ≫ ψ) wc
  have s₁ : φ₂ ≫ (fst u.A u.A).left = (fst o.A o.A).left ≫ ψ := pullback.lift_fst _ _ _
  have s₂ : φ₂ ≫ (snd u.A u.A).left = (snd o.A o.A).left ≫ ψ := pullback.lift_snd _ _ _
  have sq : IsSquare ψ φ₂ := ⟨s₁, s₂⟩
  have a₁ : (φ₂ ≫ φ₂u) ≫ (fst A₀ A₀).left = φ₂o ≫ (fst A₀ A₀).left := by
    rw [Category.assoc, squ.1, ← Category.assoc, s₁, Category.assoc, hψ, sqo.1]
  have a₂ : (φ₂ ≫ φ₂u) ≫ (snd A₀ A₀).left = φ₂o ≫ (snd A₀ A₀).left := by
    rw [Category.assoc, squ.2, ← Category.assoc, s₂, Category.assoc, hψ, sqo.2]
  have e₂ : φ₂ ≫ φ₂u = φ₂o := Over.tensorObj_ext _ _ a₁ a₂
  have i₂ : LBIso (P₀.pull φ₂o) (u.P.pull φ₂) :=
    LBIso.chartPull (chartPullSame P₀ _ _ _ φ₂ (fun _ => e₂.symm)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull u.P φ₂ φ₂ rfl) (LBIso.symm iu)
  have pol : LBIso o.P (u.P.pull φ₂) :=
    LBIso.trans o.isLB (pull_isLB hP₀ _) (pull_isLB u.isLB _) io i₂
  exact ⟨{ φ := ψ, φ₂ := φ₂, cart := cart, sq := sq, act := hact, pol := pol, eta := heta }, rfl⟩

end GlobalTheory.HTObjMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocus
section
noncomputable section

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieAt_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} {R' : Type} [CommRing R']
    {β : R →+* R'} {x : Sp R' ⟶ S} (h : LieHer b act β x) : LieAt b act β x := by
  have H := (h R' (RingHom.id R')).1
  have e : spMap (RingHom.id R') = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

theorem lieMult_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} (k : Type) [Field k]
    [IsAlgClosed k] {β : R →+* k} {x : Sp k ⟶ S} (h : LieHer b act β x) (i : Fin D.a) :
    LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  have H := (h k (RingHom.id k)).2 k (RingHom.id k) i
  have e : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

end GlobalTheory.HTMkObj

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem exists_obj_of_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  intro p _ D R _ b N _ _ h M B _ ζ S s₁ t c e he hc X πX AX _ _ φX φ₂X actX ηX hX sqX hRos hEta Z j hLie hGeom
  let A' := (Over.pullback (j ≫ πX)).obj c.A
  let φ := PullbackComparison.pφ (j ≫ πX) c.A
  let φ₂ := PullbackComparison.pφ₂ (j ≫ πX) c.A
  have pb : IsGrpPullback A' c.A (j ≫ πX) φ := PullbackComparison.isGrpPullback (j ≫ πX) c.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare (j ≫ πX) c.A
  have wψ : φ ≫ c.A.hom = (A'.hom ≫ j) ≫ πX := by
    rw [Category.assoc]; exact pb.1.w
  let ψ : A'.left ⟶ AX.left := hX.1.lift φ (A'.hom ≫ j) wψ
  have hψ : ψ ≫ φX = φ := hX.1.lift_fst _ _ _
  have hψh : ψ ≫ AX.hom = A'.hom ≫ j := hX.1.lift_snd _ _ _
  have pbj : IsGrpPullback A' AX j ψ := IsGrpPullback.cancel hX (by rw [hψ]; exact pb) hψh
  let ψ₂ : (G2 A').left ⟶ (G2 AX).left :=
    pullback.lift ((fst A' A').left ≫ ψ) ((snd A' A').left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hψh, ← Category.assoc, ← Category.assoc, Over.w (fst A' A'),
        Over.w (snd A' A')])
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hψ₂ : ψ₂ ≫ φ₂X = φ₂ := by
    refine pullback.hom_ext (f := c.A.hom) (g := c.A.hom) ?_ ?_
    · show (ψ₂ ≫ φ₂X) ≫ (fst c.A c.A).left = φ₂ ≫ (fst c.A c.A).left
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sq.1]
    · show (ψ₂ ≫ φ₂X) ≫ (snd c.A c.A).left = φ₂ ≫ (snd c.A c.A).left
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sq.2]
  have hab : IsAbelianScheme A' :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := GlobalTheory.ActPull.exists_act_pull X Z j AX A' ψ pbj D.Oᵐᵒᵖ
    (fun a => actX.act a.unop) (fun a => actX.hom _) (by simpa using actX.one)
    (fun a b => by simpa using actX.mul b.unop a.unop) (fun a b => by simpa using actX.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ ψ = ψ ≫ (actX.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := c.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB c.isLB φ₂
  have iso : LBIso P' (c.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have hPX : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso P' ((c.P.pull φ₂X).pull ψ₂) :=
    LBIso.chartPull (chartPullSame c.P (fun _ : PUnit => φ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => (Category.comp_id _).symm))
      (chartPullLinComb c.P φ₂X (fun _ : PUnit => ψ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => by rw [hψ₂, Category.comp_id]))
      (PullbackComparison.gen_refl _ (pull_isLB c.isLB _))
  have dgX := SiegelPull.diag_iso sqψ H
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 AX ⟶ AX), x'.left ≫ ψ = ψ₂ ≫ x.left → y'.left ≫ ψ = ψ₂ ≫ y.left →
      (lift x' y').left ≫ ψ₂ = ψ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sqψ (T := Over.mk (ψ₂ ≫ (G2 AX).hom)) (T' := G2 A') (𝟙 _)
      x' y' (Z := G2 AX) ψ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  have rosP : RosatiFor D actN ((c.P.pull φ₂X).pull ψ₂) := fun a => LBIso.chartPull
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.1, Category.assoc])
      (by rw [sqψ.2])))
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by rw [sqψ.1]) (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.2, Category.assoc])))
    (hRos a)
  obtain ⟨t₁, ht₁⟩ := c.rig₁
  obtain ⟨t₂, ht₂⟩ := c.rig₂
  let u : Obj b N ((j ≫ πX) ≫ t) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id (j ≫ πX) c.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one (j ≫ πX) c.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
        (chartPullLinComb c.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap (j ≫ πX) c.A)) c.symm
      ample := (pol_pull S Z c.A A' (j ≫ πX) φ _ _ (pull_isLB c.isLB _) (pull_isLB hP' _) c.ab pb dg).2.1 hc.1
      kerP := ⟨e, he, fun T x hx => kerBy_pull pb sq c.isLB hP' iso e hc.2 T x hx⟩
      rosati := RosatiFor.of_iso (pull_isLB hPX _) hP' (LBIso.symm H) rosP
      lie := fun R' _ β x hx v hv => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pbj (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ j)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := lieAt_of_lieHer b (hLie R' β x hx') (e v)
          ((HTPull.isTanScal_iff pbj actX actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (HTPull.isTanScal_iff pbj actX actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) X Z AX A' j ψ (actX.toF D) (actN.toF D) pbj
          (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (lieMult_of_lieHer b k (hLie k β x hx') i)
      eta := fun y => SiegelPull.secPull pbj (ηX y)
      eta_add := fun y z => SiegelPull.push_injective pbj _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', hEta.1, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pbj _ (by
        rw [HTPull.push_comp pbj (hact c), push_secPull', push_secPull', hEta.2.1, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pbj _ (by
        rw [push_secPull', hEta.2.2, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨I, hI⟩ := hGeom k x β hx'
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ j) ⟶ AX) := MulEquiv.ofBijective (pushHom pbj (Over.mk x))
          ⟨SiegelPull.push_injective pbj _, SiegelPull.push_surjective pbj _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ actX.act c := fun c g => HTPull.push_comp pbj (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ ψ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm X Z AX A' j ψ _ _ (pull_isLB hPX _)
                    (pull_isLB hP' _) pbj dgX (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pbj (ηX y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pbj (ηX y) (Over.mk x)).symm }
  exact ⟨u, ψ, φ₂, pbj, by rw [hψ]; exact sq, iso, hact, fun y => SiegelPull.secPull_left pbj _⟩

end GlobalTheory.HTMkObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.PreEtaPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this


omit [GrpObj A] [GrpObj A'] in
theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end GlobalTheory.PreEtaPull

namespace GlobalTheory.UPel.HT

open GlobalTheory.PreEtaPull

theorem exists_preEta_of_siegPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  intro p _ D R _ b N h M B _ ζ S s₁ t c e he hK X πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hP : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso (c.P.pull φ₂X) (c.P.pull φ₂X) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ hP
  refine ⟨{
    A := AX
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
    act := actX
    P := c.P.pull φ₂X
    isLB := hP
    rig₁ := by
      obtain ⟨t₁, ht₁⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_one_id hpb hsq) t₁ ht₁
    rig₂ := by
      obtain ⟨t₂, ht₂⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_id_one hpb hsq) t₂ ht₂
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ φ₂X fun _ => lift_swap hsq) c.symm
    ample := (GlobalTheory.pol_pull S X c.A AX πX φX c.diag _ (pull_isLB c.isLB _) (pull_isLB hP _) c.ab hpb
      (GlobalTheory.SiegelPull.diag_iso hsq H)).2.1 hK.1
    kerP := ⟨e, he, kerBy_pull hpb hsq c.isLB hP H e hK.2⟩
    rosati := hros
    eta := ηX
    eta_add := heta.1
    eta_lin := heta.2.1
    eta_ker := heta.2.2 }, fun k _ x => Iff.rfl⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomTrivIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincarePull

theorem exists_hom_triv_iff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (D : Over (Sp R)) [GrpObj D] (Q : LB (A ⊗ D).left), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsDual D A (GlobalTheory.AbDual.swap Q) →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ P : LB (A ⊗ A).left, P.IsLB →
    HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∃ x : A ⟶ D, IsMonHom x ∧ ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (HasGen (P.pull (lift (fst A T) (snd A T ≫ y)).left) ↔ y ≫ x = 1) := by
  intro R _ A _ hA D _ Q q q' L hL aL P hP h₁ h₂
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL aL hL aL
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP a₁ a₂
  refine ⟨x, hx, fun T y ↦ ?_⟩
  have k := GlobalTheory.AbDual.triv_ev_iff hP (fst A T) (snd A T ≫ y)
  rw [GlobalTheory.BirigidLift.evc_of_cls q.isLB hP e, Category.assoc, ← GlobalTheory.AbDual.triv_ev_iff q.isLB] at k
  refine k.trans ⟨fun h ↦ q.eq_one (y ≫ x) h, fun h ↦ ?_⟩
  rw [h, GlobalTheory.AbDual.triv_ev_iff q.isLB, MonObj.comp_one]
  exact GlobalTheory.AbDual.evc_one_right q.isLB q.zero _

end GlobalTheory.PoincarePull
end
end

