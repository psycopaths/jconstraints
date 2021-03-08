/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gov.nasa.jpf.constraints.util;

import static java.nio.charset.StandardCharsets.UTF_8;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;

/**
 * Utilities pertaining to character set aware I/O operations. These can be used to replace
 * operations implicitly using the platform charset with little extra boilerplate code.
 *
 * <p>This class only replicates functionality existing in Java SE 11 and above and should be
 * removed if Java 8 support is dropped.
 */
public final class CharsetIO {

  /** Disabled default constructor. */
  private CharsetIO() {
    throw new AssertionError("Utility class initialized");
  }

  /**
   * Create a {@link PrintStream} writing to the given file with UTF-8 encoding.
   *
   * <p>This suppresses the {@link UnsupportedEncodingException} declared by {@link
   * PrintStream#PrintStream(File, String)} (which cannot occur for UTF-8!), since the safe
   * constructor API {@link PrintStream#PrintStream(File, Charset)} is not available for Java 8.
   *
   * @param file the file to write to.
   * @return the wrapped stream.
   * @throws FileNotFoundException if the file does not exist.
   */
  public static PrintStream openInPrintStream(File file) throws FileNotFoundException {
    try {
      return new PrintStream(file, UTF_8.name());
    } catch (UnsupportedEncodingException e) {
      throw new AssertionError("Standard charset unavailable");
    }
  }

  /**
   * Wrap a given stream into a {@link PrintStream} with UTF-8 encoding.
   *
   * <p>This suppresses the {@link UnsupportedEncodingException} declared by {@link
   * PrintStream#PrintStream(OutputStream, boolean, String)} (which cannot occur for UTF-8!), since
   * the safe constructor API {@link PrintStream#PrintStream(OutputStream, boolean, Charset)} is not
   * available for Java 8.
   *
   * @param stream the stream to wrap.
   * @return the wrapped stream.
   */
  public static PrintStream wrapInPrintStream(OutputStream stream) {
    try {
      return new PrintStream(stream, false, UTF_8.name());
    } catch (UnsupportedEncodingException e) {
      throw new AssertionError("Standard charset unavailable");
    }
  }

  /**
   * Create a {@link BufferedReader} for the given file's contents, parsed as UTF-8.
   *
   * @param file the file to read.
   * @return a wrapping reader.
   * @throws FileNotFoundException if the file does not exist.
   */
  public static BufferedReader readFile(File file) throws FileNotFoundException {
    return new BufferedReader(new InputStreamReader(new FileInputStream(file), UTF_8));
  }

  /**
   * Create a {@link BufferedReader} for the given file's contents, parsed as UTF-8.
   *
   * @param filename the name fo the file to read.
   * @return a wrapping reader.
   * @throws FileNotFoundException if the file does not exist.
   */
  public static BufferedReader readFile(String filename) throws FileNotFoundException {
    return new BufferedReader(new InputStreamReader(new FileInputStream(filename), UTF_8));
  }
}
