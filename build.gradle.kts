/*
 * Copyright 2017-2021 The jConstraints-cvc4 Authors
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

import org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED
import org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED
import org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED
import org.gradle.api.tasks.testing.logging.TestLogEvent.STANDARD_ERROR
import java.time.LocalDate.now

plugins {
    `java-library`
    id("com.github.johnrengelman.shadow") version "5.2.0"
    id("org.cadixdev.licenser") version "0.5.0"
}

repositories {
    maven { url = uri("https://jitpack.io") }
    mavenLocal()
    mavenCentral()
}

dependencies {

    //Use jitpack.io until a better solution is in place for jConstraints
    implementation("com.github.tudo-aqua:jconstraints:b057fe7")
    implementation("solver:CVC4-gpl:1.8.0")
    implementation("org.apache.commons:commons-math3:3.6.1")

    testImplementation("org.testng:testng:7.0.0")
}

val test by tasks.getting(Test::class) {
    // Use TestNG for unit tests
    useTestNG()
    testLogging {
        events(FAILED, STANDARD_ERROR, SKIPPED, PASSED)
    }
}

tasks.shadowJar {
    exclude("tools.aqua:jconstraints:.*")

}

license {
    header = project.file("contrib/license-header.txt")
    ext["year"] = now().year

    exclude("**/*.smt2", "**/*.txt")

    tasks {
        create("buildFiles") {
            files = project.files("build.gradle.kts", "settings.gradle.kts")
        }
    }
}
