package gov.nasa.jpf.constraints.types;

import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;

public class NamedSort implements Type<Void> {

  private String name;

  public NamedSort(String name) {
    this.name = name;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public String[] getOtherNames() {
    return new String[0];
  }

  @Override
  public Class<Void> getCanonicalClass() {
    return null;
  }

  @Override
  public Class<?>[] getOtherClasses() {
    return new Class[0];
  }

  @Override
  public Void cast(Object other) {
    return null;
  }

  @Override
  public Void getDefaultValue() {
    return null;
  }

  @Override
  public Type<?> getSuperType() {
    return null;
  }

  @Override
  public <O> CastOperation<? super O, ? extends Void> cast(Type<O> fromType) {
    return null;
  }

  @Override
  public <O> CastOperation<? super O, ? extends Void> requireCast(Type<O> fromType) {
    return null;
  }

  @Override
  public Void parse(String string) throws ImpreciseRepresentationException {
    return null;
  }
}
